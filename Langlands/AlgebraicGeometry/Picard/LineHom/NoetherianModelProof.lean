import Langlands.AlgebraicGeometry.Picard.LineHom.TensorComparison
import Langlands.AlgebraicGeometry.Picard.LineHom.TestCoordinates
import Langlands.AlgebraicGeometry.Picard.LineHom.FreeKernel
import Langlands.AlgebraicGeometry.Picard.LineHom.CechModel
import Langlands.AlgebraicGeometry.Picard.LineHom.AffineExtension
import Langlands.AlgebraicGeometry.Picard.LineHom.NoetherianModelStatement
import Langlands.AlgebraicGeometry.Modules.BiCech.Kunneth

/-! # Finite linear models of line-bundle Hom over a Noetherian affine base

Let `p : Y ⟶ Spec R` be proper and flat with `R` Noetherian, and let `L`, `M` be locally free of
rank one on `Y`. Choose a finite ordered affine cover `𝒰` of `Y` with frames `e i` of `L` and
`f i` of `M` on its members, with transition functions `α` and `β`. A two-term complex
`d : C0 → C1` of `R`-modules with a map to the gauge complex of `α`, `β` that is bijective on
kernels after every base change (`exists_gauge_model`), together with a finite linear system
`a` whose solutions are the kernels of `d` after base change (`exists_kernel_solutions_model`),
gives a natural map from the solutions of `a` to the Hom presheaf: a solution over a test `T`
goes to the morphism of pulled-back line bundles whose frame coordinates are the image of the
corresponding kernel element in the gauge coordinates of `T ×_{Spec R} Y`. It is bijective on
affine tests, hence an isomorphism of fppf sheaves.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.LineHom

open CocycleGluing FiniteLinearEquations CoherentSheaves

section Model

attribute [local instance] FiniteLinearEquations.sectionsAlgebra

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))
  {𝒰 : Y.OrderedAffineCover} {L M : Y.Modules} {e : ∀ i, Γ(L, 𝒰.U i)} {f : ∀ i, Γ(M, 𝒰.U i)}
  (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (𝒰.U i))
  (hf : ∀ i, Scheme.Modules.IsFrameOn (f i) (𝒰.U i))
  {α β : ∀ i j : 𝒰.ι, (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ} (hα : IsTransition e α) (hβ : IsTransition f β)
  {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
  {d : C0 →ₗ[R] C1} {ψ0 : C0 →ₗ[R] GaugeC0 p 𝒰} {ψ1 : C1 →ₗ[R] GaugeC1 p 𝒰}
  (comm : gaugeD p α β ∘ₗ ψ0 = ψ1 ∘ₗ d)
  {m n : ℕ} {a : Fin m → Fin n → R}
  (E : ∀ (S : Type u) [CommRing S] [Algebra R S],
    (TensorProduct.map (LinearMap.id : S →ₗ[R] S) d).ker ≃ Solutions a S)

/-- The gauge family attached to a solution over a test `T`: the image in the gauge coordinates
of `T ×_{Spec R} Y` of the corresponding kernel element. -/
def modelFamily (T : Over (Spec (.of R))) (x : Solutions a Γ(T.left, ⊤)) :
    {b : ∀ i, Γ(pullback T.hom p, pullback.snd T.hom p ⁻¹ᵁ 𝒰.U i) //
      IsGaugeFamily (pullbackCocycle (pullback.snd T.hom p) α)
        (pullbackCocycle (pullback.snd T.hom p) β) b} :=
  ⟨tensorGauge0 p 𝒰 T (ψ0.lTensor Γ(T.left, ⊤) ((E Γ(T.left, ⊤)).symm x)), by
    rw [← pulledGaugeD_eq_zero_iff _ (isCocycle_of_isTransition he hα)
      (isCocycle_of_isTransition hf hβ), pulledGaugeD_tensorGauge0, ← LinearMap.comp_apply,
      ← LinearMap.lTensor_comp, comm, LinearMap.lTensor_comp, LinearMap.comp_apply]
    have h : d.lTensor Γ(T.left, ⊤) ((E Γ(T.left, ⊤)).symm x) = 0 :=
      LinearMap.mem_ker.1 ((E Γ(T.left, ⊤)).symm x).2
    rw [h, map_zero, map_zero]⟩

variable (hE : ∀ (S S' : Type u) [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
    (q : S →ₐ[R] S') (z : (TensorProduct.map (LinearMap.id : S →ₗ[R] S) d).ker),
    E S' (TensorKernel.mapKernel d q.toLinearMap z) = mapSolutions a q (E S z))
include hE

omit hE in
lemma lTensor_map_pullSections {T' T : Over (Spec (.of R))} (g : T' ⟶ T)
    (w : Γ(T.left, ⊤) ⊗[R] C0) :
    ψ0.lTensor Γ(T'.left, ⊤) (TensorProduct.map (pullSections g).toLinearMap LinearMap.id w) =
      TensorProduct.map (pullSections g).toLinearMap LinearMap.id (ψ0.lTensor Γ(T.left, ⊤) w) := by
  induction w with
  | tmul x c => rfl
  | add w w' hw hw' => simp only [map_add, hw, hw']

omit hE in
lemma preimage_le_map_preimage {T' T : Over (Spec (.of R))} (g : T' ⟶ T) (U : Y.Opens) :
    pullback.snd T'.hom p ⁻¹ᵁ U ≤
      ((Over.pullback p).map g).left ⁻¹ᵁ (pullback.snd T.hom p ⁻¹ᵁ U) :=
  ((congrArg (fun q ↦ q ⁻¹ᵁ U) (Over.w ((Over.pullback p).map g)).symm).trans
    (Scheme.Hom.comp_preimage _ _ _)).le

/-- The gauge families of solutions are natural in the test. -/
lemma modelFamily_naturality {T' T : Over (Spec (.of R))} (g : T' ⟶ T)
    (x : Solutions a Γ(T.left, ⊤)) (i : 𝒰.ι)
    (h : pullback.snd T'.hom p ⁻¹ᵁ 𝒰.U i ≤
      ((Over.pullback p).map g).left ⁻¹ᵁ (pullback.snd T.hom p ⁻¹ᵁ 𝒰.U i)) :
    (modelFamily p he hf hα hβ comm E T' (mapSolutions a (pullSections g) x)).1 i =
      ((Over.pullback p).map g).left.appLE (pullback.snd T.hom p ⁻¹ᵁ 𝒰.U i)
        (pullback.snd T'.hom p ⁻¹ᵁ 𝒰.U i) h ((modelFamily p he hf hα hβ comm E T x).1 i) := by
  have hz : (E Γ(T'.left, ⊤)).symm (mapSolutions a (pullSections g) x) =
      TensorKernel.mapKernel d (pullSections g).toLinearMap ((E Γ(T.left, ⊤)).symm x) := by
    rw [Equiv.symm_apply_eq, hE, Equiv.apply_symm_apply]
  change tensorGauge0 p 𝒰 T' (ψ0.lTensor _
    ((E Γ(T'.left, ⊤)).symm (mapSolutions a (pullSections g) x))) i = _
  rw [hz]
  change tensorGauge0 p 𝒰 T' (ψ0.lTensor _ (TensorProduct.map (pullSections g).toLinearMap
    LinearMap.id ((E Γ(T.left, ⊤)).symm x).1)) i = _
  rw [lTensor_map_pullSections, tensorGauge0_naturality p g _ i h]
  rfl

/-- The frame-coordinate description of a solution is natural in the test. -/
lemma modelMap_naturality_down {T' T : Over (Spec (.of R))} (g : T' ⟶ T)
    (x : Solutions a Γ(T.left, ⊤)) :
    (pullbackFrameHomEquiv he hf hα hβ 𝒰.iSup_eq_top (pullback.snd T'.hom p)).symm
        (modelFamily p he hf hα hβ comm E T' (mapSolutions a (pullSections g) x)) =
      Langlands.Scheme.Modules.transport ((Over.pullback p).map g).left
        (Over.w ((Over.pullback p).map g)) (Over.w ((Over.pullback p).map g))
        ((pullbackFrameHomEquiv he hf hα hβ 𝒰.iSup_eq_top (pullback.snd T.hom p)).symm
          (modelFamily p he hf hα hβ comm E T x)) := by
  rw [Equiv.symm_apply_eq]
  apply Subtype.ext
  funext i
  refine (modelFamily_naturality p he hf hα hβ comm E hE g x i
    (preimage_le_map_preimage p g (𝒰.U i))).trans ?_
  refine Eq.trans ?_ (pullbackFrameHomEquiv_transport he hf hα hβ 𝒰.iSup_eq_top
    ((Over.pullback p).map g).left (pullback.snd T.hom p) (pullback.snd T'.hom p)
    (Over.w ((Over.pullback p).map g)) _ i).symm
  erw [Equiv.apply_symm_apply]

/-- The comparison map from the solutions of `a` to the Hom presheaf. -/
def modelMap : solutionsPresheaf a ⟶ intrinsicModuleHomPresheaf p L M where
  app T := ↾fun x ↦ ULift.up ((pullbackFrameHomEquiv he hf hα hβ 𝒰.iSup_eq_top
    (pullback.snd T.unop.hom p)).symm (modelFamily p he hf hα hβ comm E T.unop x.down))
  naturality T T' g := by
    ext x
    apply ULift.ext
    exact (modelMap_naturality_down p he hf hα hβ comm E hE g.unop x.down).trans
      (intrinsicModuleHomPresheaf_map_down p L M g.unop _).symm

variable {comm} in
omit hE in
/-- On affine tests the gauge families of solutions are all gauge families, each exactly once. -/
lemma modelFamily_bijective [IsSeparated p]
    (hbij : ∀ (A : Type u) [CommRing A] [Algebra R A],
      Function.Bijective (TwoChartCech.kerMapBaseChange d (gaugeD p α β) ψ0 ψ1 comm A))
    (T : Over (Spec (.of R))) [IsAffine T.left] :
    Function.Bijective (modelFamily p he hf hα hβ comm E T) := by
  let S := Γ(T.left, ⊤)
  have hbase : ∀ {P Q : Type u} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
      (φ : P →ₗ[R] Q) (z : S ⊗[R] P), φ.baseChange S z = φ.lTensor S z := fun φ z ↦
    congrFun (LinearMap.baseChange_eq_ltensor φ) z
  constructor
  · intro x y hxy
    have h0 := (tensorGauge0_bijective p T).1 (congrArg Subtype.val hxy)
    have h1 : TwoChartCech.kerMapBaseChange d (gaugeD p α β) ψ0 ψ1 comm S
        ⟨((E S).symm x).1,
          LinearMap.mem_ker.2 ((hbase d _).trans (LinearMap.mem_ker.1 ((E S).symm x).2))⟩ =
        TwoChartCech.kerMapBaseChange d (gaugeD p α β) ψ0 ψ1 comm S
        ⟨((E S).symm y).1,
          LinearMap.mem_ker.2 ((hbase d _).trans (LinearMap.mem_ker.1 ((E S).symm y).2))⟩ := by
      apply Subtype.ext
      exact (hbase ψ0 _).trans (h0.trans (hbase ψ0 _).symm)
    have h2 := congrArg Subtype.val ((hbij S).1 h1)
    exact (E S).symm.injective (Subtype.ext h2)
  · rintro ⟨b, hb⟩
    rw [← pulledGaugeD_eq_zero_iff _ (isCocycle_of_isTransition he hα)
      (isCocycle_of_isTransition hf hβ)] at hb
    obtain ⟨w, hw⟩ := (tensorGauge0_ker_bijective p α β T).2 ⟨b, hb⟩
    obtain ⟨z, hz⟩ := (hbij S).2
      ⟨w.1, LinearMap.mem_ker.2 ((hbase (gaugeD p α β) _).trans (LinearMap.mem_ker.1 w.2))⟩
    refine ⟨E S ⟨z.1,
      LinearMap.mem_ker.2 ((hbase d z.1).symm.trans (LinearMap.mem_ker.1 z.2))⟩, ?_⟩
    apply Subtype.ext
    change tensorGauge0 p 𝒰 T (ψ0.lTensor S ((E S).symm (E S _))) = b
    rw [Equiv.symm_apply_apply]
    have hz' : ψ0.lTensor S z.1 = w.1 := by
      rw [← hbase]; exact congrArg Subtype.val hz
    change tensorGauge0 p 𝒰 T (ψ0.lTensor S z.1) = b
    rw [hz']
    exact congrArg Subtype.val hw

variable {comm} in
include he hf hα hβ in
/-- **Finite linear model from frames and a gauge model.** -/
theorem hasModel_of_gaugeModel [IsSeparated p] [M.IsQuasicoherent]
    (hbij : ∀ (A : Type u) [CommRing A] [Algebra R A],
      Function.Bijective (TwoChartCech.kerMapBaseChange d (gaugeD p α β) ψ0 ψ1 comm A)) :
    HasModel (intrinsicModuleHomPresheaf p L M) := by
  let Ψ := modelMap p he hf hα hβ comm E hE
  have hF : CategoryTheory.Presheaf.IsSheaf (AlgebraicSpace.fppfTopology (Spec (.of R)))
      (solutionsPresheaf a) :=
    (CategoryTheory.Presheaf.isSheaf_of_iso_iff (solutionsPresheafIso a)).1
      ((AlgebraicSpace.schemeSheaf _).obj (equationsScheme a)).property
  have hG := (intrinsicModuleHomSheaf p L M).property
  have : IsIso Ψ := isIso_of_bijective_affine hF hG Ψ fun T hT ↦ by
    change Function.Bijective (fun x : ULift.{u + 1} (Solutions a Γ(T.left, ⊤)) ↦
      ULift.up.{u + 1} ((pullbackFrameHomEquiv he hf hα hβ 𝒰.iSup_eq_top
        (pullback.snd T.hom p)).symm (modelFamily p he hf hα hβ comm E T x.down)))
    exact Equiv.ulift.symm.bijective.comp ((Equiv.bijective _).comp
      ((modelFamily_bijective p he hf hα hβ E hbij T).comp Equiv.ulift.bijective))
  exact ⟨m, n, a, ⟨(asIso Ψ).symm⟩⟩

end Model

section Frames

open Langlands.AlgebraicGeometry.Modules.BiCech in
/-- Two locally free sheaves of rank one on a quasi-compact scheme have frames on the members
of a common finite ordered affine cover. -/
theorem exists_frameCover₂ {X : Scheme.{u}} [CompactSpace X] {L M : X.Modules}
    (hL : IsLocallyFreeRankOne L) (hM : IsLocallyFreeRankOne M) :
    ∃ 𝒰 : X.OrderedAffineCover, ∀ i, (∃ e : Γ(L, 𝒰.U i), Scheme.Modules.IsFrameOn e (𝒰.U i)) ∧
      ∃ f : Γ(M, 𝒰.U i), Scheme.Modules.IsFrameOn f (𝒰.U i) := by
  classical
  let B : Set X.Opens := {U | IsAffineOpen U ∧ (∃ e : Γ(L, U), Scheme.Modules.IsFrameOn e U) ∧
    ∃ f : Γ(M, U), Scheme.Modules.IsFrameOn f U}
  have hB : TopologicalSpace.Opens.IsBasis B := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro W x hx
    obtain ⟨T, hxT, e, he⟩ := exists_isFrameOn_of_isLocallyFreeRankOne hL x
    obtain ⟨T', hxT', f, hf⟩ := exists_isFrameOn_of_isLocallyFreeRankOne hM x
    obtain ⟨U, hU, hxU, hUWT⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
        (show x ∈ W ⊓ (T ⊓ T') from ⟨hx, hxT, hxT'⟩)
    have hT : U ≤ T := hUWT.trans (inf_le_right.trans inf_le_left)
    have hT' : U ≤ T' := hUWT.trans (inf_le_right.trans inf_le_right)
    exact ⟨U, ⟨hU, ⟨L.presheaf.map (homOfLE hT).op e, (he.map _).mono hT⟩,
      ⟨M.presheaf.map (homOfLE hT').op f, (hf.map _).mono hT'⟩⟩, hxU, hUWT.trans inf_le_left⟩
  obtain ⟨Us, hUs, hfinite, hcover⟩ :=
    hB.exists_finite_of_isCompact (U := ⊤) (show IsCompact (⊤ : X.Opens).carrier from
      isCompact_univ)
  let : Fintype Us := hfinite.fintype
  let : LinearOrder Us :=
    LinearOrder.lift' (Fintype.equivFin Us) (Fintype.equivFin Us).injective
  exact ⟨{
    ι := Us
    U := Subtype.val
    isAffineOpen := fun i => (hUs i.property).1
    iSup_eq_top := by
      simpa only [sSup_eq_iSup'] using hcover.symm }, fun i => (hUs i.property).2⟩

end Frames

/-- **Noetherian models of line-bundle Hom.** Over a Noetherian affine base, the Hom presheaf of
two locally free sheaves of rank one on a proper flat scheme is, naturally on the entire slice,
the solution presheaf of finitely many homogeneous linear equations. -/
theorem noetherianModel : NoetherianModelStatement.{u} := by
  intro R hR Y p hp hflat L M hL hM
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨𝒰, h𝒰⟩ := exists_frameCover₂ hL hM
  choose e he using fun i ↦ (h𝒰 i).1
  choose f hf using fun i ↦ (h𝒰 i).2
  have hα := isTransition_frameCocycle he
  have hβ := isTransition_frameCocycle hf
  obtain ⟨G, ψ0, ψ1, comm, hbij⟩ := exists_gauge_model (R := R) p 𝒰 (frameCocycle e he)
    (frameCocycle f hf) (isCocycle_of_isTransition he hα) (isCocycle_of_isTransition hf hβ)
  obtain ⟨m, n, a, E, hE⟩ := exists_kernel_solutions_model G.d
  have := hM.isQuasicoherent
  exact hasModel_of_gaugeModel p he hf hα hβ E hE hbij

end Langlands.AlgebraicGeometry.Picard.LineHom
