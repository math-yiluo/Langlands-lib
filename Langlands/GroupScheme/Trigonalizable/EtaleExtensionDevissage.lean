import Langlands.GroupScheme.Rational.SplitUnipotentExtensionSection
import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorProof
import Langlands.GroupScheme.LinearKernelTowerSection

/-! # Dévissage of unipotent extension splitting to vector kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.EtaleExtensionSplit

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private theorem range_kernel_factored {E Q H V : GroupScheme (Spec (CommRingCat.of k))}
    (q : E ⟶ H) (r : E ⟶ Q) (q' : Q ⟶ H) (hfac : r ≫ q' = q)
    (z : V ⟶ kernel q)
    (hr : SubgroupFunctor.range (kernelι r) = SubgroupFunctor.range (z ≫ kernelι q)) :
    SubgroupFunctor.range (kernelι (FactoredKernel.map q r q' hfac)) =
      SubgroupFunctor.range z := by
  let p := FactoredKernel.map q r q' hfac
  ext T x
  change x ∈ (SubgroupFunctor.range (kernelι p)).carrier T ↔ _
  have hx : (x ≫ p.hom.hom) ≫ (kernelι q').hom.hom =
      (x ≫ (kernelι q).hom.hom) ≫ r.hom.hom := by
    simp only [Category.assoc, ← Grp.comp_hom_hom, p, FactoredKernel.map_comp]
  have hmem : x ≫ (kernelι q).hom.hom ∈ (SubgroupFunctor.range (kernelι r)).carrier T ↔
      x ≫ p.hom.hom = 1 := by
    rw [mem_range_kernelι_iff, ← hx, ← MonObj.one_comp (f := (kernelι q').hom.hom)]
    exact (cancel_mono (kernelι q').hom.hom)
  rw [mem_range_kernelι_iff, ← hmem, hr]
  constructor
  · intro hx'
    obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hx'
    exact SubgroupFunctor.mem_range.mpr
      ⟨v, (cancel_mono (kernelι q).hom.hom).mp (by simpa only [Grp.comp_hom_hom,
        Category.assoc] using hv)⟩
  · intro hx'
    obtain ⟨v, rfl⟩ := SubgroupFunctor.mem_range.mp hx'
    exact SubgroupFunctor.mem_range.mpr ⟨v, (Category.assoc _ _ _).symm⟩

/-- For a fixed affine quotient, it suffices to split the extensions whose full
kernel is a vector group. The acting extension group need not be connected. -/
theorem exists_section_of_vector_splitting [PerfectField k]
    (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom]
    (hvector : ∀ (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
      (f : G ⟶ H) [Smooth f.hom.hom.left] [Surjective f.hom.hom.left] {n : ℕ},
        RelativeRoot.IsVectorGroupOfDimension (kernel f) n → ∃ s : H ⟶ G, s ≫ f = 𝟙 H)
    (E : GroupScheme (Spec (CommRingCat.of k))) [Smooth E.X.hom] [IsAffineHom E.X.hom]
    (q : E ⟶ H) [Smooth q.hom.hom.left] [Surjective q.hom.hom.left]
    [ConnectedSpace (kernel q).X.left] (hU : IsUnipotent (kernel q)) :
    ∃ s : H ⟶ E, s ≫ q = 𝟙 H := by
  have hind : ∀ d : ℕ,
      ∀ (E : GroupScheme (Spec (CommRingCat.of k)))
        (hsm : Smooth E.X.hom) (haff : IsAffineHom E.X.hom)
        (q : E ⟶ H) (hqsm : Smooth q.hom.hom.left)
        (hqsurj : Surjective q.hom.hom.left) (hUconn : ConnectedSpace (kernel q).X.left),
        IsUnipotent (kernel q) → SmoothOfRelativeDimension d (kernel q).X.hom →
        ∃ s : H ⟶ E, s ≫ q = 𝟙 H := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro E hsm haff q hqsm hqsurj hUconn hU hd
      let : Smooth E.X.hom := hsm
      let : IsAffineHom E.X.hom := haff
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
      · have hUsplit : RelativeRoot.IsSplitUnipotent (kernel q) :=
          perfectFieldUnipotentSplit k (kernel q) hUconn hU
        let a := VectorExtensionDescent.action (kernelι q) q rfl
        obtain ⟨V, z, aV, n, e, hz, hVsm, hVaff, _hVconn, _hV, _hVsplit,
            _hcentral, _hstableV, _hnontriv, hpos, hn, he, heq⟩ :=
          RelativeRoot.splitUnipotentStableVectorSubgroup k (kernel q) inferInstance inferInstance
            hUconn hU hUsplit htriv E hsm haff a
        let : Smooth V.X.hom := hVsm
        let : IsAffineHom V.X.hom := hVaff
        let : IsClosedImmersion z.hom.hom.left := hz
        let : Mono z.hom.hom := Over.mono_of_mono_left _
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
        obtain ⟨Q, r, hQsm, hQaff, hr⟩ := normalSubgroupQuotient k E V i hi hinormal
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
        let : Smooth r.hom.hom.left := hr.smooth_of_smooth_kernel ⟨inferInstance, rfl⟩ hVsm
        have hk : kernelι r ≫ q = 0 := by
          apply (Grp.forget _).map_injective
          change (kernelι r).hom.hom ≫ q.hom.hom = 1
          apply (mem_range_kernelι_iff q _).mp
          have hx : (kernelι r).hom.hom ∈ (SubgroupFunctor.range i).carrier (kernel r).X := by
            rw [← hr.2.2.2]
            exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
          obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hx
          rw [← hv]
          exact SubgroupFunctor.mem_range.mpr ⟨v ≫ z.hom.hom, Category.assoc _ _ _⟩
        let q' := FpqcHomDescent.hom r q hk
        have hfac : r ≫ q' = q := FpqcHomDescent.fac r q hk
        have hfacs : r.hom.hom.left ≫ q'.hom.hom.left = q.hom.hom.left :=
          congrArg (fun f => f.hom.hom.left) hfac
        let : Smooth (r.hom.hom.left ≫ q'.hom.hom.left) := hfacs.symm ▸ hqsm
        let : Smooth q'.hom.hom.left :=
          Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
            r.hom.hom.left q'.hom.hom.left
        let : Surjective q'.hom.hom.left := by
          have hc : Surjective (r.hom.hom.left ≫ q'.hom.hom.left) := hfacs.symm ▸ hqsurj
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
        let : QuasiCompact p.hom.hom.left := by
          have hc : QuasiCompact (p.hom.hom.left ≫ (kernel q').X.hom) := by
            rw [Over.w p.hom.hom]
            infer_instance
          let : QuasiCompact (p.hom.hom.left ≫ (kernel q').X.hom) := hc
          exact QuasiCompact.of_comp _ (kernel q').X.hom
        have hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) p :=
          ⟨inferInstance, inferInstance, inferInstance, range_kernel_factored q r q' hfac z hr.2.2.2⟩
        have hpdim := hp.smoothOfRelativeDimension_of_kernel ⟨inferInstance, rfl⟩ hn
        obtain ⟨m, hm⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
          (kernel q').X.left _ (kernel q').X.hom inferInstance inferInstance
        let : SmoothOfRelativeDimension n p.hom.hom.left := hpdim
        let : SmoothOfRelativeDimension m (kernel q').X.hom := hm
        have hsum : SmoothOfRelativeDimension (n + m) (kernel q).X.hom := by
          rw [← Over.w p.hom.hom]
          infer_instance
        have hdm : d = n + m := RelativeRoot.relativeDimension_eq (kernel q).X.hom hd hsum
        obtain ⟨s, hs⟩ := ih m (by omega) Q hQsm hQaff q' inferInstance inferInstance
          inferInstance hU' hm
        have hsclosed : IsClosedSubgroup s := LinearKernelTower.isClosedSubgroup_of_section q' s hs
        let : IsAffineHom (SubgroupPreimage.groupScheme r s).X.hom :=
          SubgroupPreimage.isAffineHom r s hsclosed
        let : Smooth (SubgroupPreimage.projection r s).hom.hom.left :=
          SubgroupPreimage.smooth_projection r s
        let : Surjective (SubgroupPreimage.projection r s).hom.hom.left :=
          SubgroupPreimage.surjective_projection r s
        have hv := SubgroupPreimage.isVectorGroupOfDimension_kernel i r s hr.2.2.2.symm ⟨e, he⟩
        obtain ⟨l, hl⟩ := hvector (SubgroupPreimage.groupScheme r s)
          (SubgroupPreimage.projection r s) hv
        refine ⟨l ≫ SubgroupPreimage.inclusion r s, ?_⟩
        rw [← hfac, Category.assoc, ← Category.assoc (SubgroupPreimage.inclusion r s),
          subgroupIntersection_condition, Category.assoc, hs, Category.comp_id]
        exact hl
  let : Smooth (kernel q).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme q) inferInstance
  obtain ⟨d, hd⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    (kernel q).X.left _ (kernel q).X.hom inferInstance inferInstance
  exact hind d E inferInstance inferInstance q inferInstance inferInstance inferInstance hU hd

end Langlands.GroupScheme.EtaleExtensionSplit
