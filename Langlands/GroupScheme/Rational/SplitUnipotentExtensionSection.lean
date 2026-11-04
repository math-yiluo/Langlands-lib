import Langlands.GroupScheme.Rational.VectorQuotientTorusLift
import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorStatement
import Langlands.GroupScheme.Rational.SplitUnipotentSurjectiveImage
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.FactoredKernel
import Langlands.GroupScheme.KernelRepresentativeTransport
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.Torus.Geometry
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Homomorphic sections of split unipotent extensions of tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace TorusUnipotentExtension

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {E H : GroupScheme (Spec (CommRingCat.of k))}

/-- A smooth surjective homomorphism with trivial full kernel is invertible. -/
theorem isIso_of_trivial_kernel (q : E ⟶ H)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    (htriv : SubgroupFunctor.range (𝟙 (kernel q)) = ⊥) : IsIso q := by
  have hm : Mono q.hom.hom := by
    constructor
    intro T x y hxy
    apply div_eq_one.mp
    have hk : x / y ∈ (SubgroupFunctor.range (kernelι q)).carrier T := by
      rw [mem_range_kernelι_iff, GrpObj.div_comp, hxy, div_self']
    obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hk
    have hv1 : v = 1 := by
      have hv' : v ∈ (SubgroupFunctor.range (𝟙 (kernel q))).carrier T :=
        SubgroupFunctor.mem_range.mpr ⟨v, Category.comp_id _⟩
      simpa only [htriv, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] using hv'
    rw [← hv, hv1, MonObj.one_comp]
  let : Mono q.hom.hom := hm
  let : Mono q.hom.hom.left := Over.mono_left_of_mono _
  let : IsIso q.hom.hom.left := Flat.isIso_of_surjective_of_mono _
  let : IsIso ((Over.forget _).map q.hom.hom) := by
    change IsIso q.hom.hom.left
    infer_instance
  let : IsIso q.hom.hom := isIso_of_reflects_iso q.hom.hom (Over.forget _)
  let e : E ≅ H := Grp.mkIso' (asIso q.hom.hom)
  change IsIso e.hom
  infer_instance

variable
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (hlinear : RelativeRoot.TorusVectorActionLinearizationStatement.{u})
    (H : GroupScheme (Spec (CommRingCat.of k))) (hH : IsTorus H)

include hstable hlinear hH

/-- Dimension induction on the actual full kernel. Stable vector subgroups
are chosen for conjugation by the whole extension group. -/
theorem exists_section_of_smooth_kernel
    (E : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth E.X.hom] [IsAffineHom E.X.hom] [ConnectedSpace E.X.left]
    (q : E ⟶ H) [Smooth q.hom.hom.left] [Surjective q.hom.hom.left]
    [ConnectedSpace (kernel q).X.left]
    (hU : IsUnipotent (kernel q)) (hUsplit : RelativeRoot.IsSplitUnipotent (kernel q)) :
    ∃ s : H ⟶ E, s ≫ q = 𝟙 H := by
  let : IsAffine H.X.left := SplittingAssembly.isAffine_of_isTorus H hH
  let : IsAffineHom H.X.hom := inferInstance
  have hind : ∀ d : ℕ,
      ∀ (E : GroupScheme (Spec (CommRingCat.of k)))
        (hsm : Smooth E.X.hom) (haff : IsAffineHom E.X.hom)
        (hconn : ConnectedSpace E.X.left)
        (q : E ⟶ H) (hqsm : Smooth q.hom.hom.left)
        (hqsurj : Surjective q.hom.hom.left)
        (hUconn : ConnectedSpace (kernel q).X.left),
        IsUnipotent (kernel q) → RelativeRoot.IsSplitUnipotent (kernel q) →
        SmoothOfRelativeDimension d (kernel q).X.hom →
          ∃ s : H ⟶ E, s ≫ q = 𝟙 H := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro E hsm haff hconn q hqsm hqsurj hUconn hU hUsplit hd
      let : Smooth E.X.hom := hsm
      let : IsAffineHom E.X.hom := haff
      let : ConnectedSpace E.X.left := hconn
      let : Smooth q.hom.hom.left := hqsm
      let : Surjective q.hom.hom.left := hqsurj
      let : ConnectedSpace (kernel q).X.left := hUconn
      let : Smooth (kernel q).X.hom :=
        MorphismProperty.of_isPullback (kernel_isPullback_scheme q) hqsm
      let : IsAffineHom (kernel q).X.hom := by
        rw [← Over.w (kernelι q).hom.hom]
        infer_instance
      let : QuasiCompact q.hom.hom.left := by
        have hc : QuasiCompact (q.hom.hom.left ≫ H.X.hom) := by
          rw [Over.w q.hom.hom]
          infer_instance
        let : QuasiCompact (q.hom.hom.left ≫ H.X.hom) := hc
        exact QuasiCompact.of_comp _ H.X.hom
      by_cases htriv : SubgroupFunctor.range (𝟙 (kernel q)) = ⊥
      · let : IsIso q := isIso_of_trivial_kernel q htriv
        exact ⟨inv q, IsIso.inv_hom_id q⟩
      · let a := VectorExtensionDescent.action (kernelι q) q rfl
        obtain ⟨V, z, aV, n, e, hz, hVsm, hVaff, _hVconn, _hV, _hVsplit,
            _hcentral, _hstableV, _hnontriv, hpos, hn, he, heq⟩ :=
          hstable k (kernel q) inferInstance inferInstance hUconn hU hUsplit htriv
            E hsm haff a
        let : Smooth V.X.hom := hVsm
        let : IsAffineHom V.X.hom := hVaff
        let : IsClosedImmersion z.hom.hom.left := hz
        let i : V ⟶ E := z ≫ kernelι q
        have hi : IsClosedSubgroup i := by
          change IsClosedImmersion (z.hom.hom.left ≫ (kernelι q).hom.hom.left)
          infer_instance
        let : IsClosedImmersion i.hom.hom.left := hi
        let : Mono i.hom.hom := Over.mono_of_mono_left _
        have hinormal : (SubgroupFunctor.range i).IsNormal := by
          intro T g x _ hx
          obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.mp hx
          refine SubgroupFunctor.mem_range.mpr ⟨aV.act g v, ?_⟩
          change (aV.act g v ≫ z.hom.hom) ≫ (kernelι q).hom.hom =
            g * ((v ≫ z.hom.hom) ≫ (kernelι q).hom.hom) * g⁻¹
          rw [heq]
          exact VectorExtensionDescent.action_act_comp (kernelι q) q rfl g _
        obtain ⟨Q, r, hQsm, hQaff, hr⟩ :=
          normalSubgroupQuotient k E V i hi hinormal
        let : Smooth Q.X.hom := hQsm
        let : IsAffineHom Q.X.hom := hQaff
        let : Flat r.hom.hom.left := hr.1
        let : Surjective r.hom.hom.left := hr.2.1
        let : QuasiCompact r.hom.hom.left := by
          have hc : QuasiCompact (r.hom.hom.left ≫ Q.X.hom) := by
            rw [Over.w r.hom.hom]
            infer_instance
          let : QuasiCompact (r.hom.hom.left ≫ Q.X.hom) := hc
          exact QuasiCompact.of_comp _ Q.X.hom
        let : ConnectedSpace Q.X.left := hr.connectedSpace
        have hrep : (SubgroupFunctor.range i).IsRepresentedBy i :=
          ⟨inferInstance, rfl⟩
        have hrdim := hr.smoothOfRelativeDimension_of_kernel hrep hn
        let : SmoothOfRelativeDimension n r.hom.hom.left := hrdim
        let : Smooth r.hom.hom.left := SmoothOfRelativeDimension.smooth n _
        have hk : kernelι r ≫ q = 0 := by
          apply (Grp.forget _).map_injective
          change (kernelι r).hom.hom ≫ q.hom.hom = 1
          apply (mem_range_kernelι_iff q _).mp
          have hx : (kernelι r).hom.hom ∈
              (SubgroupFunctor.range i).carrier (kernel r).X := by
            rw [← hr.2.2.2]
            exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
          obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hx
          rw [← hv]
          exact SubgroupFunctor.mem_range.mpr
            ⟨v ≫ z.hom.hom, Category.assoc _ _ _⟩
        let q' := FpqcHomDescent.hom r q hk
        have hfac : r ≫ q' = q := FpqcHomDescent.fac r q hk
        have hfacs : r.hom.hom.left ≫ q'.hom.hom.left = q.hom.hom.left :=
          congrArg (fun f => f.hom.hom.left) hfac
        let : Smooth (r.hom.hom.left ≫ q'.hom.hom.left) := hfacs.symm ▸ hqsm
        let : Smooth q'.hom.hom.left :=
          Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
            r.hom.hom.left q'.hom.hom.left
        let : Surjective q'.hom.hom.left := by
          have hc : Surjective (r.hom.hom.left ≫ q'.hom.hom.left) :=
            hfacs.symm ▸ hqsurj
          refine ⟨fun y => ?_⟩
          obtain ⟨x, hx⟩ := hc.surj y
          exact ⟨r.hom.hom.left x, hx⟩
        let : Smooth (kernel q').X.hom :=
          MorphismProperty.of_isPullback (kernel_isPullback_scheme q') inferInstance
        let : IsAffineHom (kernel q').X.hom := by
          rw [← Over.w (kernelι q').hom.hom]
          infer_instance
        let p := FactoredKernel.map q r q' hfac
        let : Smooth p.hom.hom.left := FactoredKernel.smooth_map q r q' hfac
        let : Surjective p.hom.hom.left := FactoredKernel.surjective_map q r q' hfac
        let : ConnectedSpace (kernel q').X.left :=
          p.hom.hom.left.surjective.connectedSpace p.hom.hom.left.continuous
        have hU' : IsUnipotent (kernel q') := hU.of_flat_surjective p
        have hUsplit' : RelativeRoot.IsSplitUnipotent (kernel q') :=
          hUsplit.of_surjective_to_smooth_affine p
        have hpdim : SmoothOfRelativeDimension n p.hom.hom.left :=
          MorphismProperty.of_isPullback (FactoredKernel.isPullback_scheme q r q' hfac)
            hrdim
        obtain ⟨m, hm⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
          (kernel q').X.left _ (kernel q').X.hom inferInstance inferInstance
        let : SmoothOfRelativeDimension n p.hom.hom.left := hpdim
        let : SmoothOfRelativeDimension m (kernel q').X.hom := hm
        have hsum : SmoothOfRelativeDimension (n + m) (kernel q).X.hom := by
          rw [← Over.w p.hom.hom]
          infer_instance
        have hdm : d = n + m :=
          RelativeRoot.relativeDimension_eq (kernel q).X.hom hd hsum
        obtain ⟨s, hs⟩ := ih m (by omega) Q hQsm hQaff inferInstance q'
          inferInstance inferInstance inferInstance hU' hUsplit' hm
        have hsclosed : IsClosedSubgroup s := by
          let : IsSeparated (s.hom.hom.left ≫ Q.X.hom) := by
            rw [Over.w s.hom.hom]
            infer_instance
          let : IsSeparated q'.hom.hom.left := by
            have hc : IsSeparated (q'.hom.hom.left ≫ H.X.hom) := by
              rw [Over.w q'.hom.hom]
              infer_instance
            let : IsSeparated (q'.hom.hom.left ≫ H.X.hom) := hc
            exact IsSeparated.of_comp _ H.X.hom
          have hs' : s.hom.hom.left ≫ q'.hom.hom.left = 𝟙 H.X.left :=
            congrArg (fun f => f.hom.hom.left) hs
          let : IsClosedImmersion (s.hom.hom.left ≫ q'.hom.hom.left) :=
            hs'.symm ▸ inferInstance
          exact IsClosedImmersion.of_comp _ q'.hom.hom.left
        obtain ⟨l, hl⟩ := hH.exists_vectorQuotientLift i r hr.2.2.2.symm
          ⟨e, he⟩ hlinear s hsclosed
        refine ⟨l, ?_⟩
        rw [← hfac, ← Category.assoc, hl, hs]
  let : Smooth (kernel q).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme q) inferInstance
  obtain ⟨d, hd⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    (kernel q).X.left _ (kernel q).X.hom inferInstance inferInstance
  exact hind d E inferInstance inferInstance inferInstance q inferInstance
    inferInstance inferInstance hU hUsplit hd

end TorusUnipotentExtension

variable {k : Type u} [Field k]
    {U E H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth E.X.hom] [IsAffineHom E.X.hom] [ConnectedSpace E.X.left]
    [Smooth U.X.hom] [ConnectedSpace U.X.left]
    (n : U ⟶ E) [Mono n.hom.hom] (q : E ⟶ H)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q)
    (hU : IsUnipotent U) (hUsplit : RelativeRoot.IsSplitUnipotent U)
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (hlinear : RelativeRoot.TorusVectorActionLinearizationStatement.{u})
    (hH : IsTorus H)

include hq hU hUsplit hstable hlinear hH in
/-- A full smooth connected split-unipotent fppf kernel admits a homomorphic
section of its torus quotient, subject to the exact stable-vector and
linearization inputs. -/
theorem IsTorus.exists_splitUnipotentExtensionSection :
    ∃ s : H ⟶ E, s ≫ q = 𝟙 H := by
  let : IsAffine H.X.left := SplittingAssembly.isAffine_of_isTorus H hH
  let : IsAffineHom H.X.hom := inferInstance
  let : QuasiCompact q.hom.hom.left := by
    have hc : QuasiCompact (q.hom.hom.left ≫ H.X.hom) := by
      rw [Over.w q.hom.hom]
      infer_instance
    let : QuasiCompact (q.hom.hom.left ≫ H.X.hom) := hc
    exact QuasiCompact.of_comp _ H.X.hom
  have hrep : (SubgroupFunctor.range n).IsRepresentedBy n :=
    ⟨inferInstance, rfl⟩
  let : Smooth q.hom.hom.left := hq.smooth_of_smooth_kernel hrep inferInstance
  let : Surjective q.hom.hom.left := hq.2.1
  let : ConnectedSpace (kernel q).X.left :=
    KernelRepresentative.connectedSpace q n hq.2.2.2
  have hK : IsUnipotent (kernel q) :=
    KernelRepresentative.isUnipotent q n hq.2.2.2 hU
  have hKsplit : RelativeRoot.IsSplitUnipotent (kernel q) :=
    hUsplit.of_iso (KernelRepresentative.iso q n hq.2.2.2).symm
  exact TorusUnipotentExtension.exists_section_of_smooth_kernel
    hstable hlinear H hH E q hK hKsplit

/-- A chosen homomorphic section over the original field. -/
def IsTorus.splitUnipotentExtensionSection : H ⟶ E :=
  Classical.choose
    (hH.exists_splitUnipotentExtensionSection n q hq hU hUsplit hstable hlinear)

/-- The chosen section composes with the original quotient to its identity. -/
theorem IsTorus.splitUnipotentExtensionSection_comp :
    hH.splitUnipotentExtensionSection n q hq hU hUsplit hstable hlinear ≫ q = 𝟙 H :=
  Classical.choose_spec
    (hH.exists_splitUnipotentExtensionSection n q hq hU hUsplit hstable hlinear)

end Langlands.GroupScheme
