import Langlands.GroupScheme.Reductive.CharacteristicZeroVectorExtensionStatement
import Langlands.GroupScheme.Rational.SplitUnipotentExtensionSection
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof

/-! # Reducing characteristic-zero unipotent extensions to vector kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] [CharZero k]

section VectorLift

variable {G V Q H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    (n : V ⟶ G) [Mono n.hom.hom] (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hn : SubgroupFunctor.range n = SubgroupFunctor.range (kernelι q))
    {d : ℕ} (hV : RelativeRoot.IsVectorGroupOfDimension V d)
    (hvector : CharacteristicZeroReductiveVectorExtensionStatement.{u})
    (j : H ⟶ Q) (hj : IsClosedSubgroup j) (hH : IsConnectedReductive H)

include hn hV hvector hj hH in
/-- The vector-extension input splits the actual inverse image of a closed
connected reductive subgroup through a full vector quotient. -/
theorem IsConnectedReductive.exists_vectorQuotientLift :
    ∃ l : H ⟶ G, l ≫ q = j := by
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : IsAffineHom (SubgroupPreimage.groupScheme q j).X.hom :=
    SubgroupPreimage.isAffineHom q j hj
  let : Flat (SubgroupPreimage.projection q j).hom.hom.left :=
    SubgroupPreimage.flat_projection q j
  let : Surjective (SubgroupPreimage.projection q j).hom.hom.left :=
    SubgroupPreimage.surjective_projection q j
  have hK := SubgroupPreimage.isVectorGroupOfDimension_kernel n q j hn hV
  obtain ⟨s, hs⟩ := hvector k (SubgroupPreimage.groupScheme q j) H
    (SubgroupPreimage.projection q j) hH d hK
  refine ⟨s ≫ SubgroupPreimage.inclusion q j, ?_⟩
  rw [Category.assoc, subgroupIntersection_condition,
    ← Category.assoc, hs, Category.id_comp]

end VectorLift

namespace CharacteristicZeroUnipotentExtension

section Induction

variable
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (hvector : CharacteristicZeroReductiveVectorExtensionStatement.{u})
    (H : GroupScheme (Spec (CommRingCat.of k))) (hH : IsConnectedReductive H)

include hstable hvector hH

/-- Dimension induction on the actual full kernel. Stable vector subgroups
are chosen for conjugation by the whole extension group. -/
theorem exists_section_of_smooth_kernel
    (E : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth E.X.hom] [IsAffineHom E.X.hom] [ConnectedSpace E.X.left]
    (q : E ⟶ H) [Smooth q.hom.hom.left] [Surjective q.hom.hom.left]
    [ConnectedSpace (kernel q).X.left]
    (hU : IsUnipotent (kernel q)) (hUsplit : RelativeRoot.IsSplitUnipotent (kernel q)) :
    ∃ s : H ⟶ E, s ≫ q = 𝟙 H := by
  let : IsAffineHom H.X.hom := hH.isAffineHom
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
      · let : IsIso q := TorusUnipotentExtension.isIso_of_trivial_kernel q htriv
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
          ⟨e, he⟩ hvector s hsclosed
        refine ⟨l, ?_⟩
        rw [← hfac, ← Category.assoc, hl, hs]
  let : Smooth (kernel q).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme q) inferInstance
  obtain ⟨d, hd⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    (kernel q).X.left _ (kernel q).X.hom inferInstance inferInstance
  exact hind d E inferInstance inferInstance inferInstance q inferInstance
    inferInstance inferInstance hU hUsplit hd

end Induction

variable
    (hstable : RelativeRoot.SplitUnipotentStableVectorSubgroupStatement.{u})
    (hvector : CharacteristicZeroReductiveVectorExtensionStatement.{u})
    (H : GroupScheme (Spec (CommRingCat.of k))) (hH : IsConnectedReductive H)
    (E : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth E.X.hom] [IsAffineHom E.X.hom] [ConnectedSpace E.X.left]
    (q : E ⟶ H) [Smooth q.hom.hom.left] [Surjective q.hom.hom.left]
    [ConnectedSpace (kernel q).X.left] (hU : IsUnipotent (kernel q))

include hstable hvector hH hU in
/-- Perfect-field splitness removes the split-series premise in characteristic
zero; the stable-vector and reductive vector-extension inputs remain explicit. -/
theorem exists_section : ∃ s : H ⟶ E, s ≫ q = 𝟙 H := by
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : Smooth (kernel q).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme q) inferInstance
  let : IsAffineHom (kernel q).X.hom := by
    rw [← Over.w (kernelι q).hom.hom]
    infer_instance
  have hsplit := perfectFieldUnipotentSplit k (kernel q) inferInstance hU
  exact exists_section_of_smooth_kernel hstable hvector H hH E q hU hsplit

/-- The chosen group section constructed by induction on the dimension of the
full unipotent kernel, conditional on the two displayed structural inputs. -/
def groupSection : H ⟶ E :=
  Classical.choose (exists_section hstable hvector H hH E q hU)

/-- The constructed section splits the original homomorphism. -/
theorem groupSection_comp : groupSection hstable hvector H hH E q hU ≫ q = 𝟙 H :=
  Classical.choose_spec (exists_section hstable hvector H hH E q hU)

end CharacteristicZeroUnipotentExtension

end Langlands.GroupScheme
