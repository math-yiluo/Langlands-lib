import Langlands.GroupScheme.Reductive.LocalSplitFlatBigCell
import Langlands.GroupScheme.Reductive.LocalSplitIntegralGeneration
import Langlands.GroupScheme.Reductive.LocalSplitCellIsomorphism
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Two-cell factorization over arbitrary local rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalSplitCell

section CoordinateLifting

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {m n : ℕ}

/-- Cell points lift whenever global functions and global units lift. -/
theorem exists_cellPoint_lift {W Z : Over (Spec (CommRingCat.of R))} (f : W ⟶ Z)
    (hf : Function.Surjective f.left.appTop)
    (hu : Function.Surjective (Units.map f.left.appTop.hom.toMonoidHom))
    (x : W ⟶ cellObj R I m n) :
    ∃ y : Z ⟶ cellObj R I m n, f ≫ y = x := by
  classical
  choose v hv using fun k : Fin m => hf (negCoord x k)
  choose w hw using fun k : Fin n => hf (posCoord x k)
  choose t ht using fun a : I => hu (splitTorus.pointsEquiv I W (torusCoord x) a)
  let t' := (splitTorus.pointsEquiv I Z).symm t
  obtain ⟨y, hy⟩ := (LocalSplitBigCell.coordTriple_bijective R I m n Z).2 (v, t', w)
  have hy' : negCoord y = v ∧ torusCoord y = t' ∧ posCoord y = w := by
    simpa only [LocalSplitBigCell.coordTriple, Prod.mk.injEq] using hy
  refine ⟨y, (LocalSplitBigCell.coordTriple_bijective R I m n W).1 ?_⟩
  apply Prod.ext
  · change negCoord (f ≫ y) = negCoord x
    rw [negCoord_comp, hy'.1]
    exact funext hv
  · apply Prod.ext
    · change torusCoord (f ≫ y) = torusCoord x
      rw [torusCoord_comp, hy'.2.1]
      apply (splitTorus.pointsEquiv I W).injective
      rw [splitTorus.pointsEquiv_naturality, MulEquiv.apply_symm_apply]
      exact funext ht
    · change posCoord (f ≫ y) = posCoord x
      rw [posCoord_comp, hy'.2.2]
      exact funext hw

/-- Every residue-field point of the coordinate cell lifts over a local ring. -/
theorem exists_cellPoint_lift_residue [IsLocalRing R]
    (x : Over.mk (Spec.algebraMap R (IsLocalRing.ResidueField R)) ⟶ cellObj R I m n) :
    ∃ y : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ cellObj R I m n,
      Over.homMk (Spec.algebraMap R (IsLocalRing.ResidueField R)) (by simp) ≫ y = x := by
  let κ := IsLocalRing.ResidueField R
  let π := Spec.algebraMap R κ
  let τ : Over.mk π ⟶ 𝟙_ (Over (Spec (CommRingCat.of R))) := Over.homMk π (by simp)
  have hπ : IsClosedImmersion π :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (algebraMap R κ))
      IsLocalRing.residue_surjective
  have hs : Function.Surjective π.appTop :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine π).2
  let : IsLocalRing Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.isLocalRing
  let : Nontrivial Γ(Spec (CommRingCat.of κ), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of κ)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have hl := IsLocalHom.of_surjective π.appTop.hom hs
  exact exists_cellPoint_lift τ hs
    (IsLocalRing.surjective_units_map_of_local_ringHom π.appTop.hom hs hl) x

end CoordinateLifting

section Factorization

variable {R : Type u} [CommRing R] [IsLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  {I : Type u} [Fintype I] {G : GroupScheme (Spec (CommRingCat.of R))} {J : Type u}

/-- Over a local ring with separably closed residue field, any open coordinate cell
gives a factorization of every base point as a product of two cell points. -/
theorem exists_two_cell_factors (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (fam : J → (Ga R ⟶ G))
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    [IsOpenImmersion (cellMap i fam neg pos).left]
    (g : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X) :
    ∃ x y : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ cellObj R I m n,
      g = (x ≫ cellMap i fam neg pos) * (y ≫ cellMap i fam neg pos) := by
  let κ := IsLocalRing.ResidueField R
  let Ω := cellMap i fam neg pos
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  let π : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R) := Spec.algebraMap R κ
  let Gκ := (GroupScheme.baseChange π).obj G
  have : Smooth Gκ.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom π))
  have : IsAffineHom Gκ.X.hom := inferInstanceAs (IsAffineHom (pullback.snd G.X.hom π))
  have hκred : IsConnectedReductive Gκ :=
    fieldReductive_of_residueReductive G Set.univ
      (fun s _ => hG.isConnectedReductive_residueFiber s) π (Set.mem_univ _)
  have : ConnectedSpace Gκ.X.left := hκred.connectedSpace
  let e := baseChangeBasePointsEquiv π G
  let τ : Over.mk π ⟶ 𝟙_ (Over (Spec (CommRingCat.of R))) := Over.homMk π (by simp)
  let r : (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X) →* (Over.mk π ⟶ G.X) :=
    { toFun := fun x => τ ≫ x
      map_one' := MonObj.comp_one τ
      map_mul' := fun x y => MonObj.comp_mul τ x y }
  have : IsLocalHom (algebraMap R κ) := inferInstanceAs (IsLocalHom (IsLocalRing.residue R))
  have hπ : π (IsLocalRing.closedPoint κ) = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (algebraMap R κ)
  have hr : ∀ x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X,
      (r x).left (IsLocalRing.closedPoint κ) = x.left (IsLocalRing.closedPoint R) := by
    intro x
    change x.left (π (IsLocalRing.closedPoint κ)) = _
    rw [hπ]
  have he : ∀ y : rationalPoints Gκ,
      (e y).left (IsLocalRing.closedPoint κ) =
        pullback.fst G.X.hom π (y.left (IsLocalRing.closedPoint κ)) := by
    intro y
    rw [baseChangeBasePointsEquiv_left]
    rfl
  let U : Set Gκ.X.left := (pullback.fst G.X.hom π) ⁻¹' Set.range Ω.left
  have hU : IsOpen U := (IsOpenImmersion.isOpen_range Ω.left).preimage
    (pullback.fst G.X.hom π).continuous
  have h0 : (e.symm (r (cellUnit R I m n ≫ Ω))).left (IsLocalRing.closedPoint κ) ∈ U := by
    change pullback.fst G.X.hom π _ ∈ Set.range Ω.left
    rw [← he, MulEquiv.apply_symm_apply, hr]
    exact ⟨_, rfl⟩
  obtain ⟨q, hqU, hqpU⟩ := exists_rationalPoint_mem_inv_mul_mem κ Gκ U hU _ h0 (e.symm (r g))
  have hq : (e q).left (IsLocalRing.closedPoint κ) ∈ Set.range Ω.left := by
    rw [he]
    exact hqU
  have hqrange : Set.range (e q).left ⊆ Set.range Ω.left := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum κ) z (IsLocalRing.closedPoint κ)]
    exact hq
  let bq : Spec (CommRingCat.of κ) ⟶ (cellObj R I m n).left :=
    IsOpenImmersion.lift Ω.left (e q).left hqrange
  have hbq : bq ≫ (cellObj R I m n).hom = π := by
    rw [← Over.w Ω, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w (e q)
  obtain ⟨x, hx⟩ := exists_cellPoint_lift_residue
    (Over.homMk bq hbq : Over.mk π ⟶ cellObj R I m n)
  let h := x ≫ Ω
  have hrh : r h = e q := by
    change τ ≫ x ≫ Ω = e q
    rw [← Category.assoc, hx]
    apply Over.OverMorphism.ext
    exact IsOpenImmersion.lift_fac _ _ _
  have hk : (h⁻¹ * g).left (IsLocalRing.closedPoint R) ∈ Set.range Ω.left := by
    rw [← hr, map_mul, map_inv, hrh, ← MulEquiv.apply_symm_apply e (r g), ← map_inv,
      ← map_mul, he]
    exact hqpU
  obtain ⟨y, hy⟩ := exists_lift_of_closedPoint_mem Ω (h⁻¹ * g) hk
  refine ⟨x, y, ?_⟩
  change g = h * (y ≫ Ω)
  rw [hy]
  group

/-- The same hypotheses imply generation by the supplied torus and additive maps. -/
theorem mem_closure_generators_of_open_cell (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (fam : J → (Ga R ⟶ G))
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    [IsOpenImmersion (cellMap i fam neg pos).left]
    (g : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X) :
    g ∈ Subgroup.closure (generators i fam) := by
  obtain ⟨x, y, hg⟩ := exists_two_cell_factors hG i fam neg pos g
  rw [hg]
  exact mul_mem (cellMap_mem_closure i fam neg pos x) (cellMap_mem_closure i fam neg pos y)

variable [IsAffineHom G.X.hom]

/-- Actual root parametrizations supply the open cell over an arbitrary local ring. -/
theorem exists_two_cell_factors_of_rootParametrizations (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base)
    (fam : J → (Ga R ⟶ G)) (hfam : ∀ α, IsRootParametrization i (P.root α) (fam α))
    {m n : ℕ} (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
    (g : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X) :
    ∃ x y : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ cellObj R I m n,
      g = (x ≫ cellMap i fam (fun k => (neg k : J)) (fun k => (pos k : J))) *
        (y ≫ cellMap i fam (fun k => (neg k : J)) (fun k => (pos k : J))) := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have := LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b fam hfam neg pos
  exact exists_two_cell_factors hG i fam _ _ g

/-- Torus and root points generate over a local ring with separably closed residue field. -/
theorem mem_closure_generators_of_isLocalRing (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base)
    (fam : J → (Ga R ⟶ G)) (hfam : ∀ α, IsRootParametrization i (P.root α) (fam α))
    (g : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X) :
    g ∈ Subgroup.closure (generators i fam) := by
  classical
  have : Finite J := hP.finite
  let neg := (Finite.equivFin {α // ¬ b.IsPos α}).symm
  let pos := (Finite.equivFin {α // b.IsPos α}).symm
  obtain ⟨x, y, hg⟩ :=
    exists_two_cell_factors_of_rootParametrizations hG i hmax P hP b fam hfam neg pos g
  rw [hg]
  exact mul_mem (cellMap_mem_closure i fam _ _ x) (cellMap_mem_closure i fam _ _ y)

end Factorization

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme

open LocalSplitCell

/-- Two-cell factorization and torus/root generation with no domain or Henselian
hypothesis on the local ring. -/
def LocalSplitLocalGenerationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (I : Type u) [Fintype I] (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
    (_ : IsReductive G) (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (_ : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)) (_ : IsFibrewiseRootDatumOf I G i P)
    (b : P.Base) (fam : J → (Ga R ⟶ G))
    (_ : ∀ α, IsRootParametrization i (P.root α) (fam α))
    (m n : ℕ) (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
    (g : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X),
    (∃ x y : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ cellObj R I m n,
      g = (x ≫ cellMap i fam (fun k => (neg k : J)) (fun k => (pos k : J))) *
        (y ≫ cellMap i fam (fun k => (neg k : J)) (fun k => (pos k : J)))) ∧
      g ∈ Subgroup.closure (generators i fam)

theorem localSplitLocalGeneration : LocalSplitLocalGenerationStatement.{u} := by
  intro R _ _ _ I _ G _ hG i hmax J P hP b fam hfam m n neg pos g
  exact ⟨exists_two_cell_factors_of_rootParametrizations hG i hmax P hP b fam hfam neg pos g,
    mem_closure_generators_of_isLocalRing hG i hmax P hP b fam hfam g⟩

end Langlands.GroupScheme
