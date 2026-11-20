import Langlands.GroupScheme.Torus.DiagonalizableProjectorChart
import Langlands.GroupScheme.Torus.OrderedProjectorAffineBaseChange
import Langlands.GroupScheme.Torus.OrderedProjectorWeightGeneration
import Langlands.GroupScheme.HomScheme.SubgroupFamilyEvaluation
import Langlands.GroupScheme.Rational.SplitRankTransport
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Étale local coverage by ordered projector charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.OrderedProjectorScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

/-- A chart for a collection of distinct weights generating the lattice of a split torus. -/
structure SplitChart where
  index : Type u
  [finiteIndex : Finite index]
  size : ℕ
  weights : Fin size → (index → ℤ)
  injective : Function.Injective weights
  generates : AddSubgroup.closure (Set.range weights) = ⊤

attribute [instance] SplitChart.finiteIndex

variable {R : CommRingCat.{u}} {n : Type} [Fintype n] [DecidableEq n]
variable {M : Over (Spec R)} {K : GroupScheme M.left}

/-- The affine ordered projector scheme of a split chart. -/
abbrev SplitChart.scheme (C : SplitChart.{u}) (n : Type) [Fintype n] [DecidableEq n]
    (R : CommRingCat.{u}) : Over (Spec R) := OrderedProjectorScheme.scheme (Fin C.size) n R

/-- The actual classifying map of a split chart. -/
def SplitChart.map (C : SplitChart.{u})
    (j : K ⟶ (baseChange M.hom).obj (GeneralLinear.groupScheme n R))
    (hu : TorusSubgroupModuli.IsUniversal j) : C.scheme n R ⟶ M := by
  classical
  letI : Fintype C.index := Fintype.ofFinite C.index
  exact chartMap C.weights j hu C.generates (Diagonalizable.isSplitTorus R (AddEquiv.refl _))

open TorusSubgroupModuli (familyHom evaluate)
open DiagonalizableProjectorWeights (chartOpen chartRing labels localGlobalFamily)

private theorem evaluate_affineRepresentation {A B : CommRingCat.{u}}
    (b : Spec A ⟶ Spec R) (c : Spec B ⟶ Spec A) {H : GroupScheme (Spec A)}
    (f : H ⟶ (baseChange b).obj (GeneralLinear.groupScheme n R))
    {Λ : Type u} [AddCommGroup Λ] (e : (Diagonalizable.groupScheme A Λ).toGrp ≅ H)
    {J : Type} [Fintype J] [DecidableEq J] (w : J → Λ) (P : Family J n Γ(Spec B, ⊤))
    (h : (baseChange c).map (e.hom ≫ f ≫ (GeneralLinear.baseChangeIso n b).hom) =
      subgroupHom w (Over.mk c) P) :
    evaluate (M := Over.mk b) f (Over.homMk c rfl : Over.mk (c ≫ b) ⟶ Over.mk b) =
      SubgroupFunctor.range (subgroupHom w (Over.mk (c ≫ b)) P) := by
  let d : Over.mk (c ≫ b) ⟶ Over.mk b := Over.homMk c rfl
  let g := GeneralLinear.baseChangeIso n b
  let dG := affineModelComparison b c g
  let dD := affineModelComparison b c (Diagonalizable.baseChangeIso b Λ)
  let e' := dD ≪≫ (baseChange c).mapIso e
  let f' := familyHom f d
  have hf : f' ≫ dG.hom = (baseChange c).map f ≫ (baseChange c).map g.hom := by
    let s := Descent.pullbackComparison b c (c ≫ b) rfl (GeneralLinear.groupScheme n R)
    change ((baseChange c).map f ≫ s.hom) ≫ (s.inv ≫ (baseChange c).map g.hom) = _
    simp
  have he : e'.hom ≫ f' = subgroupHom w (Over.mk (c ≫ b)) P := by
    apply (cancel_mono dG.hom).mp
    rw [Category.assoc, hf]
    change e'.hom ≫ (baseChange c).map f ≫ (baseChange c).map g.hom =
      subgroupHom w (Over.mk (c ≫ b)) P ≫ dG.hom
    rw [subgroupHom_affineModelComparison b c w P, ← h]
    simp only [e', Iso.trans_hom, Functor.mapIso_hom, Category.assoc, Functor.map_comp]
    rfl
  change SubgroupFunctor.range f' = _
  rw [← he, SubgroupFunctor.range_iso_comp]

/-- Every point of the moduli has an étale neighborhood whose classifying map factors through
an ordered projector chart. -/
theorem exists_etale_factorization_through_splitChart
    (j : K ⟶ (baseChange M.hom).obj (GeneralLinear.groupScheme n R))
    (hj : IsClosedSubgroup j) (hK : RelativeTorus.IsTorus K)
    (hu : TorusSubgroupModuli.IsUniversal j) (x : M.left) :
    ∃ (C : SplitChart.{u}) (V : Over (Spec R)) (p : V ⟶ C.scheme n R),
      Etale ((p ≫ C.map j hu).left) ∧ x ∈ Set.range (p ≫ C.map j hu).left := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hK
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  let 𝒱 := (𝒰.X i).affineCover
  obtain ⟨k, z, rfl⟩ := 𝒱.exists_eq y
  let A : CommRingCat.{u} := Γ(𝒱.X k, ⊤)
  let v : Spec A ⟶ 𝒰.X i := (𝒱.X k).isoSpec.inv ≫ 𝒱.f k
  let z₀ : Spec A := (𝒱.X k).isoSpec.hom z
  have hz₀ : v z₀ = 𝒱.f k z := by
    change 𝒱.f k (((𝒱.X k).isoSpec.hom ≫ (𝒱.X k).isoSpec.inv) z) = _
    rw [Iso.hom_inv_id]
    rfl
  let q := v ≫ 𝒰.f i
  let b := q ≫ M.hom
  let T := Over.mk b
  let a : T ⟶ M := Over.homMk q rfl
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  have : Etale q := by dsimp only [q, v]; infer_instance
  have hsplit : IsSplitTorus ((baseChange q).obj K) :=
    IsSplitTorus.of_iso (baseChangeCompIso (𝒰.f i) v K) ((h𝒰 i).baseChange v)
  obtain ⟨I, hI, ⟨e₀⟩⟩ := hsplit
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let Λ := I → ℤ
  let e : (Diagonalizable.groupScheme A Λ).toGrp ≅ (baseChange q).obj K :=
    Diagonalizable.splitIso A (AddEquiv.refl Λ) ≪≫ e₀.symm
  let ρ : MatrixRepresentation (Diagonalizable.groupScheme A Λ).toGrp n :=
    e.hom ≫ familyHom j a ≫ (GeneralLinear.baseChangeIso n b).hom
  have hρ : IsClosedSubgroup ρ := (IsClosedSubgroup.of_iso e).comp
    ((TorusSubgroupModuli.isClosedSubgroup_familyHom j hj a).comp_iso
      (GeneralLinear.baseChangeIso n b))
  let c := chartOpen ρ z₀
  let W := Over.mk c
  let V := Over.mk (c ≫ b)
  let d : V ⟶ T := Over.homMk c rfl
  let P := localGlobalFamily ρ z₀
  let w := labels ρ z₀
  have hc : (baseChange c).map ρ = subgroupHom w W P :=
    DiagonalizableProjectorWeights.baseChange_eq_subgroupHom ρ z₀
  have hz : z₀ ∈ Set.range c := by
    let r := DiagonalizableProjectorWeights.awayElement ρ z₀
    change (z₀ : PrimeSpectrum A) ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away r)))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact DiagonalizableProjectorWeights.awayElement_notMem ρ z₀
  obtain ⟨t, ht⟩ := hz
  let : Nonempty W.left := ⟨t⟩
  have hw : AddSubgroup.closure (Set.range w) = ⊤ :=
    closure_weights_eq_top_of_isClosedSubgroup W w P (hc ▸ IsClosedSubgroup.baseChange c hρ)
  let C : SplitChart.{u} :=
    { index := I
      size := _
      weights := w
      injective := DiagonalizableProjectorWeights.labels_injective ρ z₀
      generates := hw }
  let p : V ⟶ C.scheme n R := (pointsEquiv (Fin C.size) n R V).symm P
  have heval : evaluate j (d ≫ a) = SubgroupFunctor.range (subgroupHom w V P) :=
    (TorusSubgroupModuli.evaluate_comp j a d).symm.trans
      (evaluate_affineRepresentation b c (familyHom j a) e w P hc)
  have hfac : p ≫ C.map j hu = d ≫ a := by
    apply (hu V _ (TorusSubgroupModuli.isAdmissible_evaluate j hj ⟨𝒰, h𝒰⟩ (d ≫ a))).unique
    · let hs := Diagonalizable.isSplitTorus R (AddEquiv.refl Λ)
      refine (evaluate_comp_chartMap w j hu hw hs p).trans ?_
      rw [show pointsEquiv (Fin C.size) n R V p = P from Equiv.apply_symm_apply _ _]
      exact heval.symm
    · rfl
  refine ⟨C, V, p, ?_, ?_⟩ <;> rw [hfac]
  · change Etale (c ≫ q)
    have : IsOpenImmersion c := DiagonalizableProjectorWeights.chartOpen_isOpenImmersion ρ z₀
    infer_instance
  · refine ⟨t, ?_⟩
    change 𝒰.f i (v (c t)) = 𝒰.f i (𝒱.f k z)
    rw [ht, hz₀]

end Langlands.GroupScheme.OrderedProjectorScheme
