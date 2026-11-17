import Langlands.GroupScheme.Reductive.SplitBorelPositiveIso
import Langlands.GroupScheme.Reductive.AffineRegularCentralizer
import Langlands.GroupScheme.Reductive.LocalSplitFlatBigCell
import Langlands.GroupScheme.Reductive.LocalSplitPositiveProducts

/-! # The closed subgroup `T ⋉ U_{Φ⁺}` over an affine base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {u : J → (Ga R ⟶ G)}

omit [IsAffineHom G.X.hom] in
/-- The ordered product over the empty family is the identity. -/
theorem orderedProduct_fin_zero (e : Fin 0 → J) (Z : Over (Spec (CommRingCat.of R)))
    (c : Fin 0 → Γ(Z.left, ⊤)) : orderedProduct u e Z c = 1 := by
  simp [orderedProduct]

omit [IsAffineHom G.X.hom] in
/-- The torus-times-positive cell map is a monomorphism as soon as some big cell containing the
same positive enumeration is an open immersion. -/
theorem cellMap_zero_mono {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    [IsOpenImmersion (cellMap i u neg pos).left] :
    Mono (cellMap i u (Fin.elim0 : Fin 0 → J) pos) := by
  have : Mono (cellMap i u neg pos) := Over.mono_of_mono_left _
  constructor
  intro Z x y h
  let s : (Z ⟶ cellObj R I 0 n) → (Z ⟶ cellObj R I m n) := fun x =>
    mkCellPoint Z 0 (splitTorus.pointsEquiv I Z (torusCoord x)) (posCoord x)
  have hs : ∀ x : Z ⟶ cellObj R I 0 n,
      s x ≫ cellMap i u neg pos = x ≫ cellMap i u (Fin.elim0 : Fin 0 → J) pos := by
    intro x
    have ht : torusCoord (s x) = torusCoord x :=
      (splitTorus.pointsEquiv I Z).injective (torusCoord_mkCellPoint _ _ _ _)
    rw [comp_cellMap, comp_cellMap, cellPoint, cellPoint, negCoord_mkCellPoint,
      posCoord_mkCellPoint, ht, orderedProduct_zero, orderedProduct_fin_zero]
  have hxy : s x = s y := (cancel_mono (cellMap i u neg pos)).mp (by rw [hs, hs, h])
  apply cellPoint_ext
  · funext k
    exact k.elim0
  · have := congrArg torusCoord hxy
    simp only [s] at this
    rw [← torusCoord_mkCellPoint Z 0 (splitTorus.pointsEquiv I Z (torusCoord x)) (posCoord x),
      ← torusCoord_mkCellPoint Z 0 (splitTorus.pointsEquiv I Z (torusCoord y)) (posCoord y),
      this]
  · have := congrArg posCoord hxy
    simp only [s, posCoord_mkCellPoint] at this
    exact this

/-- **The closed subgroup `T ⋉ U_{Φ⁺}`** (Conrad, *Reductive group schemes*, Proposition
5.1.14 for the positive system of a base). For a base `b` and an enumeration `pos` of the
positive roots, the map `(t, w) ↦ i(t) ∏ₖ u_{pos k}(wₖ)` is an isomorphism onto the closed
dynamic parabolic subgroup of a cocharacter which is positive exactly on the `b`-positive
roots. -/
theorem exists_closedSubgroup_torus_positive (hG : IsReductive G)
    (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (u α))
    (b : P.Base) (n : ℕ) (pos : Fin n ≃ {α // b.IsPos α}) :
    ∃ (B : GroupScheme (Spec (CommRingCat.of R))) (jB : B ⟶ G)
      (φ : cellObj R I 0 n ≅ B.X),
      IsClosedSubgroup jB ∧
        φ.hom ≫ jB.hom.hom = cellMap i u (Fin.elim0 : Fin 0 → J) (fun k => (pos k : J)) := by
  classical
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Fintype J := @Fintype.ofFinite J hP.finite
  let neg := (Fintype.equivFin {α // ¬ b.IsPos α}).symm
  have hopen := LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b u hv neg pos
  let pos' : Fin n → J := fun k => (pos k : J)
  let neg' : Fin (Fintype.card {α // ¬ b.IsPos α}) → J := fun k => (neg k : J)
  have : IsOpenImmersion (cellMap i u neg' pos').left := hopen
  obtain ⟨d, hd, ν, hν⟩ := exists_coPairing_eq_height P b
  have hneg : ∀ k, coPairing (P.root (neg' k)) ν < 0 := by
    intro k
    rw [hν]
    have h1 := (neg k).2
    rw [RootPairing.Base.isPos_iff] at h1
    have h2 := b.height_ne_zero (neg' k)
    have h3 : b.height (neg' k) < 0 := by simp only [neg'] at h2 ⊢; omega
    nlinarith
  have hpos : ∀ k, 0 < coPairing (P.root (pos' k)) ν := by
    intro k
    rw [hν]
    have h1 := (pos k).2
    rw [RootPairing.Base.isPos_iff] at h1
    exact mul_pos hd h1
  have hreg : ∀ a : J, ∑ j, P.root a j * ν j ≠ 0 := by
    intro a
    change coPairing (P.root a) ν ≠ 0
    rw [hν]
    exact mul_ne_zero hd.ne' (b.height_ne_zero a)
  let χ := AffineRegularBorel.cocharacter i ν
  have hcent : Dynamic.centralizer χ = SubgroupFunctor.range i :=
    AffineRegularBorel.centralizer_eq_range i ν P hP hreg hG hi hmax
  have hu : TorusEquivariant i (fun α => P.root α) u := fun α Z t c => (hv α).equivariant Z t c
  let B := Dynamic.Affine.parabolicScheme χ
  let jB : B ⟶ G := Dynamic.Affine.parabolicHom χ
  have hB : (Dynamic.parabolic χ).IsRepresentedBy jB := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have hBc : IsClosedSubgroup jB := Dynamic.Affine.isClosedSubgroup_parabolicHom χ
  have : IsClosedImmersion jB.hom.hom.left := hBc
  have : IsAffineHom B.X.hom := by
    rw [← Over.w jB.hom.hom]
    infer_instance
  have : IsAffine B.X.left := isAffine_of_isAffineHom B.X.hom
  have hjmono : Mono jB.hom.hom := Over.mono_of_mono_left _
  have hcmono : Mono (cellMap i u (Fin.elim0 : Fin 0 → J) pos') := cellMap_zero_mono neg' pos'
  -- the cell map lands in the parabolic
  have hmemP : cellMap i u (Fin.elim0 : Fin 0 → J) pos' ∈
      (Dynamic.parabolic χ).carrier (cellObj R I 0 n) := by
    rw [← Category.id_comp (cellMap i u (Fin.elim0 : Fin 0 → J) pos'), comp_cellMap, cellPoint,
      orderedProduct_fin_zero, one_mul]
    refine Subgroup.mul_mem _ ?_ ?_
    · apply Dynamic.centralizer_le_parabolic χ
      rw [hcent]
      exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
    · exact Dynamic.unipotent_le_parabolic χ _ (orderedProduct_mem_unipotent hu ν pos' hpos _ _)
  rw [← hB.2] at hmemP
  obtain ⟨f, hf⟩ := SubgroupFunctor.mem_range.mp hmemP
  -- decompose the universal point of the parabolic
  have hg : jB.hom.hom ∈ (Dynamic.parabolic χ).carrier B.X := by
    rw [← hB.2]
    exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨l, hl⟩ := Dynamic.exists_hasLimit χ hg
  have hlc : l ∈ (Dynamic.centralizer χ).carrier B.X := hl.mem_centralizer χ
  have hlinv : l⁻¹ ∈ (Dynamic.centralizer χ).carrier B.X := Subgroup.inv_mem _ hlc
  have hU : l⁻¹ * jB.hom.hom ∈ (Dynamic.unipotent χ).carrier B.X := by
    have h := (Dynamic.hasLimit_of_mem_centralizer χ hlinv).mul χ hl
    rwa [inv_mul_cancel] at h
  rw [hcent] at hlc
  obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.mp hlc
  obtain ⟨c, hc⟩ := exists_orderedProduct_eq_of_mem_unipotent_of_affine (pos := pos')
    hu ν hneg _ hU
  let ψ : B.X ⟶ cellObj R I 0 n := mkCellPoint B.X 0 (splitTorus.pointsEquiv I B.X t) c
  have hψ : ψ ≫ cellMap i u (Fin.elim0 : Fin 0 → J) pos' = jB.hom.hom := by
    have htc : torusCoord ψ = t :=
      (splitTorus.pointsEquiv I B.X).injective (torusCoord_mkCellPoint _ _ _ _)
    rw [comp_cellMap, cellPoint, orderedProduct_fin_zero, one_mul, htc, posCoord_mkCellPoint,
      ← hc, ht, mul_inv_cancel_left]
  refine ⟨B, jB, ⟨f, ψ, ?_, ?_⟩, hBc, hf⟩
  · apply (cancel_mono (cellMap i u (Fin.elim0 : Fin 0 → J) pos')).mp
    rw [Category.assoc, hψ, hf, Category.id_comp]
  · apply (cancel_mono jB.hom.hom).mp
    rw [Category.assoc, hf, hψ, Category.id_comp]

end LocalSplitCell

end Langlands.GroupScheme
