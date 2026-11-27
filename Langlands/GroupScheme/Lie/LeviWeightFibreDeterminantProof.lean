import Langlands.GroupScheme.Lie.LeviWeightFibreDeterminantStatement
import Langlands.GroupScheme.Lie.StableSubspaceDeterminantBaseChange
import Langlands.GroupScheme.Torus.CentralWeightStability
import Langlands.GroupScheme.Torus.WeightSpaceScalarExtension
import Langlands.GroupScheme.Torus.WeightRestriction
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Proof of the determinant characters of weight spaces of a central split torus

The witness is the determinant of `M` acting through `l` and the adjoint representation on the
weight space `𝔤_β` of the central split torus `A`. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

set_option maxHeartbeats 800000
set_option maxRecDepth 8192

/-- A sum of weight spaces of a split torus has a basis of weight vectors whose weights add up
to the sum of the summands' characters, each counted with the dimension of its weight space. -/
theorem exists_weightBasis_of_eq_iSup {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] {S : CommGroupScheme (Spec (CommRingCat.of K))}
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (P : characterLattice S → Prop)
    (W : Submodule K (Additive (lieKernel G K)))
    (hW : W = ⨆ α : {α // P α}, weightSpace i α.val) :
    ∃ (J : Type u) (_ : Fintype J) (_ : DecidableEq J) (e : Module.Basis J K W)
      (w : J → characterLattice S),
      (∀ j, ((e j : W) : Additive (lieKernel G K)) ∈ weightSpace i (w j)) ∧
        ∑ j, w j = ∑ᶠ (α) (_ : P α), (Module.finrank K (weightSpace i α) : ℤ) • α := by
  classical
  have hint := isInternal_weightSpace_of_isSplitTorus K G S hS i
  have hfin : {α : characterLattice S | weightSpace i α ≠ ⊥}.Finite :=
    Submodule.finite_ne_bot_of_iSupIndep hint.submodule_iSupIndep
  let t : Finset (characterLattice S) := hfin.toFinset.filter P
  let J := Σ α : t, Fin (Module.finrank K (weightSpace i α.val))
  let E := hint.collectedBasis (fun α => Module.finBasis K (weightSpace i α))
  let g : J → Σ α : characterLattice S, Fin (Module.finrank K (weightSpace i α)) :=
    fun p => ⟨p.1.val, p.2⟩
  have hg : Function.Injective g := by
    rintro ⟨⟨α, hα⟩, a⟩ ⟨⟨β, hβ⟩, c⟩ h
    simp only [g, Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    rw [heq_eq_eq] at h
    subst h
    rfl
  let v : J → Additive (lieKernel G K) := fun p => E (g p)
  have hvE (p : J) : v p = (Module.finBasis K (weightSpace i p.1.val) p.2 :
      Additive (lieKernel G K)) := by
    simp only [v, E, g, DirectSum.IsInternal.collectedBasis_coe]
  have hv : LinearIndependent K v := E.linearIndependent.comp g hg
  have hmem (p : J) : v p ∈ weightSpace i p.1.val := by
    rw [hvE]
    exact Submodule.coe_mem _
  have hPt {α : characterLattice S} (hα : α ∈ t) : P α := (Finset.mem_filter.mp hα).2
  have hspan : Submodule.span K (Set.range v) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      rw [hW]
      exact Submodule.mem_iSup_of_mem (⟨p.1.val, hPt p.1.property⟩ : {α // P α}) (hmem p)
    · rw [hW]
      refine iSup_le fun α => ?_
      intro x hx
      by_cases hbot : weightSpace i α.val = ⊥
      · rw [hbot, Submodule.mem_bot] at hx
        rw [hx]
        exact Submodule.zero_mem _
      · have hαt : α.val ∈ t := Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hbot, α.property⟩
        have hx' : (⟨x, hx⟩ : weightSpace i α.val) ∈
            Submodule.span K (Set.range (Module.finBasis K (weightSpace i α.val))) := by
          rw [(Module.finBasis K _).span_eq]
          trivial
        have hmap := Submodule.mem_map_of_mem (f := (weightSpace i α.val).subtype) hx'
        rw [Submodule.map_span] at hmap
        refine Submodule.span_mono ?_ hmap
        rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨⟨⟨α.val, hαt⟩, a⟩, hvE _⟩
  let e : Module.Basis J K W := (Module.Basis.span hv).map (LinearEquiv.ofEq _ _ hspan)
  have he (p : J) : ((e p : W) : Additive (lieKernel G K)) = v p := by
    simp only [e, Module.Basis.map_apply, Module.Basis.span_apply, LinearEquiv.coe_ofEq_apply]
  refine ⟨J, inferInstance, inferInstance, e, fun p => p.1.val, fun p => ?_, ?_⟩
  · rw [he]
    exact hmem p
  · rw [finsum_cond_eq_sum_of_cond_iff (t := t)]
    · rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [Finset.sum_coe_sort t (fun α => Module.finrank K (weightSpace i α) • α)]
      refine Finset.sum_congr rfl fun α _ => ?_
      exact (natCast_zsmul _ _).symm
    · intro α hα
      have hbot : weightSpace i α ≠ ⊥ := by
        intro hb
        apply hα
        rw [hb, finrank_bot, Nat.cast_zero, zero_smul]
      constructor
      · intro hP
        exact Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hbot, hP⟩
      · exact hPt

/-- **Determinant characters of weight spaces of a central split torus.** The determinant of
`M` on the `β`-weight space of `A` in `Lie G` is a rational character whose base change restricts
to any split torus through which `A` factors as the dimension-weighted sum of the finer
weights over `β`. -/
theorem leviWeightFibreDeterminant : LeviWeightFibreDeterminantStatement.{u} := by
  intro k K _ _ _ G _ _ M _ l A a hA ha f BC β
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : IsAffineHom (BC.obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom f)
    infer_instance
  have : LocallyOfFiniteType (BC.obj G).X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom f)
    infer_instance
  have : IsAffine (BC.obj M).X.left := by
    change IsAffine (pullback M.X.hom f)
    infer_instance
  have hV := isAdjointStable_weightSpace_of_isCentral G l a hA ha β
  refine ⟨Lie.stableDeterminantCharacter hV, ?_⟩
  intro S s j hS hjs
  let βK := characterLattice.baseChange f A β
  let VK := weightSpace (BC.map (a ≫ l)) βK
  let bV := Module.finBasis k (weightSpace (a ≫ l) β)
  let bK : Module.Basis _ K VK :=
    (bV.baseChange K).map (weightSpaceBaseChangeEquiv (K := K) hA (a ≫ l) β)
  have hb : ∀ i, (bK i : Additive (lieKernel (BC.obj G) K)) =
      Lie.schemeScalarExtension (K := K) G (1 ⊗ₜ[k] (bV i : Additive (lieKernel G k))) := by
    intro i
    simp only [bK, Module.Basis.map_apply, Module.Basis.baseChange_apply]
    exact weightSpaceBaseChangeEquiv_tmul (K := K) hA (a ≫ l) β 1 (bV i)
  have hVK := Lie.isAdjointStable_baseChange hb hV
  rw [Lie.baseChange_stableDeterminantCharacter hb hV hVK]
  have hAK : IsSplitTorus ((CommGroupScheme.baseChange f).obj A).toGrp := hA.baseChange f
  have hmap : BC.map (a ≫ l) = CommGroupScheme.groupHom j ≫ s ≫ BC.map l := by
    rw [Functor.map_comp, ← Category.assoc, hjs]
    rfl
  have hVKeq : VK = ⨆ α : {α : characterLattice S // j ≫ α = βK},
      weightSpace (s ≫ BC.map l) α.val := by
    change weightSpace (BC.map (a ≫ l)) βK = _
    rw [hmap]
    exact weightSpace_comp_eq_iSup hS hAK j (s ≫ BC.map l) βK
  obtain ⟨J, _, _, e, w, he, hsum⟩ :=
    exists_weightBasis_of_eq_iSup hS (s ≫ BC.map l) (fun α => j ≫ α = βK) VK hVKeq
  have : IsAffineHom S.toGrp.X.hom := hS.isAffineHom
  have : IsAffine S.X.left := isAffine_of_isAffineHom S.toGrp.X.hom
  rw [Lie.characterRestrict_stableDeterminantCharacter hVK s e w he, map_sum]
  simp only [AddEquiv.apply_symm_apply]
  exact hsum

end Langlands.GroupScheme
