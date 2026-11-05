import Langlands.AlgebraicGeometry.ProjectiveSpace.WeightBlockPoints
import Langlands.GroupScheme.ProjectiveTorusFixedPointDimensionStatement
import Langlands.GroupScheme.ProjectiveOrbitRationalPoints

/-! # Fixed rational points of a matrix-equivariant closed subscheme of projective space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

variable {K : Type u} [Field K] {n : ℕ}

/-- Two points of projective space with the same homogeneous coordinates are equal. -/
theorem HasCoordinates.eq {x y : ProjectiveSpace K n} {c : Fin (n + 1) → K}
    (hx : HasCoordinates x c) (hy : HasCoordinates y c) : x = y := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d f hf
  have hf' : f.IsHomogeneous d := (MvPolynomial.mem_homogeneousSubmodule d f).mp hf
  rw [hx d f hf', hy d f hf']

theorem linearActionIso_inv_apply_linearAction
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) (y : ProjectiveSpace K n) :
    (linearActionIso K n e).inv (linearAction K n e y) = y := by
  change ((linearActionIso K n e).hom ≫ (linearActionIso K n e).inv) y = y
  rw [Iso.hom_inv_id]
  rfl

theorem linearAction_linearActionIso_inv_apply
    (e : (Fin (n + 1) → K) ≃ₗ[K] (Fin (n + 1) → K)) (y : ProjectiveSpace K n) :
    linearAction K n e ((linearActionIso K n e).inv y) = y := by
  change ((linearActionIso K n e).inv ≫ (linearActionIso K n e).hom) y = y
  rw [Iso.inv_hom_id]
  rfl

end Langlands.AlgebraicGeometry.ProjectiveSpace

namespace Langlands.GroupScheme.ProjectiveTorusFixedPoint

open ProjectiveOrbit Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.ProjectiveSpace

variable {k : Type u} [Field k] {n : ℕ} {X : Over (Spec (CommRingCat.of k))}

/-- The morphism from `X` to polynomial projective space underlying a morphism to the ambient
relative projective space. -/
def embedding (φ : X ⟶ ambient n (CommRingCat.of k)) : X.left ⟶ ProjectiveSpace k n :=
  φ.left ≫ RelativeProjectiveSpace.toPolynomial n (𝟙 (Spec (CommRingCat.of k)))

theorem embedding_toSpec (φ : X ⟶ ambient n (CommRingCat.of k)) :
    embedding φ ≫ projectiveSpaceToSpec k n = X.hom := by
  rw [embedding, Category.assoc, RelativeProjectiveSpace.toPolynomial_toSpec, Category.comp_id]
  exact Over.w φ

theorem isClosedImmersion_embedding (φ : X ⟶ ambient n (CommRingCat.of k))
    [IsClosedImmersion φ.left] : IsClosedImmersion (embedding φ) := by
  rw [embedding, RelativeProjectiveSpace.toPolynomial, RelativeProjectiveSpace.map_id,
    Category.id_comp]
  infer_instance

/-- The projective section of a rational point of the ambient space is that point. -/
theorem pointSection_eq
    (y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ ambient n (CommRingCat.of k)) :
    pointSection y = y.left := by
  apply RelativeProjectiveSpace.hom_ext
  · rw [pointSection, RelativeProjectiveSpace.lift_toBase]
    exact (Over.w y).symm
  · simp [pointSection]

variable {H : GroupScheme (Spec (CommRingCat.of k))} {a : SchemeAction H X}
    {ρ : MatrixRepresentation H (Fin (n + 1))} {φ : X ⟶ ambient n (CommRingCat.of k)}

/-- **Equivariance on rational points.** Translating a rational point of `X` by a rational
point `h` of the group becomes the projective linear action of the matrix `ρ(h)`. -/
theorem act_embedding (hφ : IsMatrixEquivariant a ρ φ)
    (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    (a.act h x).left ≫ embedding φ =
      x.left ≫ embedding φ ≫
        ProjectiveSpace.linearAction k n (coordinateEquiv n (ρ.rationalMatrix h)) := by
  have key := hφ _ h x
  have e1 : (a.act h x).left ≫ embedding φ =
      (a.act h x ≫ φ).left ≫ RelativeProjectiveSpace.toPolynomial n (𝟙 _) := by
    rw [embedding, Over.comp_left, Category.assoc]
  rw [e1, key, pointSection_eq, Category.assoc, Category.assoc,
    RelativeProjectiveSpace.map_toPolynomial]
  change (x ≫ φ).left ≫ matrixAction n _ ≫
    RelativeProjectiveSpace.toPolynomial n (𝟙 _ ≫ 𝟙 _) = _
  rw [Category.comp_id, matrixAction_toPolynomial, Over.comp_left, embedding]
  simp only [Category.assoc]
  rfl

theorem act_embedding_apply (hφ : IsMatrixEquivariant a ρ φ)
    (h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    embedding φ ((a.act h x).left (IsLocalRing.closedPoint k)) =
      ProjectiveSpace.linearAction k n (coordinateEquiv n (ρ.rationalMatrix h))
        (embedding φ (x.left (IsLocalRing.closedPoint k))) := by
  have h1 := congrArg (fun f => f (IsLocalRing.closedPoint k)) (act_embedding hφ h x)
  simpa only [Scheme.Hom.comp_apply] using h1

/-- A point of the image of `X` with homogeneous coordinates is the image of a rational point
of `X`. -/
theorem exists_rationalPoint [IsAlgClosed k] (φ : X ⟶ ambient n (CommRingCat.of k))
    [LocallyOfFiniteType (embedding φ)] {y : ProjectiveSpace k n} {c : Fin (n + 1) → k}
    (hy : HasCoordinates y c) (hyX : y ∈ Set.range (embedding φ)) :
    ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X,
      embedding φ (x.left (IsLocalRing.closedPoint k)) = y := by
  have hc := hy.ne_zero
  set r : Spec (CommRingCat.of k) ⟶ ProjectiveSpace k n :=
    Proj.fromOfGlobalSections (projectiveSpaceGrading k n)
      ((fieldToGlobal k).comp (MvPolynomial.eval c))
      (irrelevant_map_eval_eq_top _ hc) with hrdef
  have hr : r (IsLocalRing.closedPoint k) = y :=
    (hasCoordinates_fromOfGlobalSections (fieldToGlobal k) c _).eq hy
  obtain ⟨q, hq⟩ := exists_rationalPoint_lift_of_mem_range (embedding φ) r
    (by rw [hr]; exact hyX)
  refine ⟨Over.homMk q ?_, ?_⟩
  · change q ≫ X.hom = 𝟙 _
    rw [← embedding_toSpec φ, ← Category.assoc, hq]
    exact fromOfGlobalSections_toSpec n hc
  · change embedding φ (q (IsLocalRing.closedPoint k)) = y
    rw [← Scheme.Hom.comp_apply, hq, hr]

/-- A conjugate `P D P⁻¹` of a diagonal matrix acts on `P`-coordinates through `D`. -/
theorem conj_diagonal_mulVec (P : GL (Fin (n + 1)) k) (D v : Fin (n + 1) → k) :
    ((P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * diagonal D *
        (↑P⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) *ᵥ
        ((P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ v) =
      (P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ (fun i => D i * v i) := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc ((P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
    diagonal D), Units.inv_mul, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  congr 1
  funext i
  exact Matrix.mulVec_diagonal _ _ _

/-- **Fixed points from a weight frame.** Let `X` be a closed subscheme of projective space,
locally of finite type over an algebraically closed field, embedded equivariantly for an action
of a smooth group `H` through a matrix representation `ρ`. Suppose a change of basis `P` and
integral weights `m` are such that every `z : kˣ` is realized by a rational point of `H` acting by
`P diag(z ^ m i) P⁻¹`, and every rational point of `H` acts by `P diag(χ) P⁻¹` with `χ` constant
on the level sets of `m`. If `X` has topological Krull dimension at least `d`, then `X` has at
least `d + 1` distinct rational points fixed by `H` on all tests. -/
theorem exists_fixed_points_of_frame [IsAlgClosed k]
    {H : GroupScheme (Spec (CommRingCat.of k))} [Smooth H.X.hom] [LocallyOfFiniteType X.hom]
    {a : SchemeAction H X} {ρ : MatrixRepresentation H (Fin (n + 1))}
    {φ : X ⟶ ambient n (CommRingCat.of k)} (hφc : IsClosedImmersion φ.left)
    (hφ : IsMatrixEquivariant a ρ φ) (P : GL (Fin (n + 1)) k) (m : Fin (n + 1) → ℤ)
    (hμ : ∀ z : kˣ, ∃ t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X,
      (ρ.rationalMatrix t : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        (P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
          Matrix.diagonal (fun i => ((z ^ m i : kˣ) : k)) *
          (↑P⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
    (hblock : ∀ t : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X, ∃ χ : Fin (n + 1) → kˣ,
      (∀ i l, m i = m l → χ i = χ l) ∧
      (ρ.rationalMatrix t : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        (P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) * Matrix.diagonal (fun i => (χ i : k)) *
          (↑P⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
    (d : ℕ) (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim X.left) :
    ∃ x : Fin (d + 1) → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X),
      Function.Injective x ∧ ∀ j, a.IsFixed (x j) := by
  classical
  have : IsClosedImmersion (embedding φ) := isClosedImmersion_embedding φ
  have : IsSeparated X.hom := by
    rw [← Over.w φ]
    infer_instance
  obtain ⟨e, he⟩ : ∃ e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k),
      ∀ v, e v = (P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ v :=
    ⟨coordinateEquiv n P, fun v => rfl⟩
  -- `Z` is the image of `X` in the coordinates given by the columns of `P`.
  set Z : Set (ProjectiveSpace k n) :=
    Set.range (embedding φ ≫ (ProjectiveSpace.linearActionIso k n e).inv) with hZdef
  have hZmem : ∀ y ∈ Z, ProjectiveSpace.linearAction k n e y ∈ Set.range (embedding φ) := by
    rintro y ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    rw [Scheme.Hom.comp_apply, linearAction_linearActionIso_inv_apply]
  have hmemZ : ∀ y, ProjectiveSpace.linearAction k n e y ∈ Set.range (embedding φ) → y ∈ Z := by
    rintro y ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [Scheme.Hom.comp_apply, hx, linearActionIso_inv_apply_linearAction]
  -- Points of `Z` with coordinates `c` come from rational points of `X` with coordinates `P c`.
  have hlift : ∀ y ∈ Z, ∀ c, HasCoordinates y c →
      ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X,
        HasCoordinates (embedding φ (x.left (IsLocalRing.closedPoint k))) (e c) := by
    intro y hy c hc
    obtain ⟨x, hx⟩ := exists_rationalPoint φ (hc.linearAction e) (hZmem y hy)
    exact ⟨x, hx ▸ hc.linearAction e⟩
  have hstable : ∀ (z : kˣ) (x : ProjectiveSpace k n) (c : Fin (n + 1) → k), x ∈ Z →
      HasCoordinates x c →
        ∀ y, HasCoordinates y (fun i => ((z ^ m i : kˣ) : k) * c i) → y ∈ Z := by
    intro z y c hy hc y' hy'
    obtain ⟨x, hx⟩ := hlift y hy c hc
    obtain ⟨t, ht⟩ := hμ z
    apply hmemZ
    refine ⟨(a.act t x).left (IsLocalRing.closedPoint k), ?_⟩
    rw [act_embedding_apply hφ]
    have hv : coordinateEquiv n (ρ.rationalMatrix t) (e c) =
        e (fun i => ((z ^ m i : kˣ) : k) * c i) := by
      rw [coordinateEquiv_apply, ht, he, he, conj_diagonal_mulVec]
    have h1 := hx.linearAction (coordinateEquiv n (ρ.rationalMatrix t))
    rw [hv] at h1
    exact h1.eq (hy'.linearAction e)
  have hgc : Topology.IsClosedEmbedding
      (embedding φ ≫ (ProjectiveSpace.linearActionIso k n e).inv) :=
    Scheme.Hom.isClosedEmbedding _
  have hdZ : (d : WithBot ℕ∞) ≤ topologicalKrullDim Z :=
    hd.trans (hgc.isInducing.codRestrict fun x => Set.mem_range_self x).topologicalKrullDim_le
  obtain ⟨c, hc0, hcZ, hcm, hcp⟩ :=
    exists_weightBlock_points Z hgc.isClosed_range m hstable d hdZ
  have hpts : ∀ j, ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X,
      HasCoordinates (embedding φ (x.left (IsLocalRing.closedPoint k))) (e (c j)) := by
    intro j
    obtain ⟨y, hy⟩ := exists_hasCoordinates (hc0 j)
    exact hlift y (hcZ j y hy) (c j) hy
  choose x hx using hpts
  refine ⟨x, fun j j' hjj' => ?_, fun j => ?_⟩
  · by_contra hne
    have h1 := hx j'
    rw [← hjj'] at h1
    obtain ⟨b, -, hb⟩ := (hx j).exists_eq_smul h1
    rw [← map_smul] at hb
    exact hcp j j' hne b (e.injective hb)
  · rw [a.isFixed_iff_rationalPoints]
    intro t
    obtain ⟨χ, hχm, hχ⟩ := hblock t
    obtain ⟨i0, hi0⟩ : ∃ i, c j i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hc0 j (funext hcon)
    have hv : coordinateEquiv n (ρ.rationalMatrix t) (e (c j)) = e ((χ i0 : k) • c j) := by
      rw [coordinateEquiv_apply, hχ, he, he, conj_diagonal_mulVec]
      congr 1
      funext i
      by_cases hi : c j i = 0
      · simp [hi]
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [hχm i i0 (hcm j i i0 hi hi0)]
    have h1 := (hx j).linearAction (coordinateEquiv n (ρ.rationalMatrix t))
    rw [hv, map_smul, ← act_embedding_apply hφ] at h1
    have h2 := (embedding φ).isClosedEmbedding.injective (h1.eq ((hx j).smul (χ i0).ne_zero))
    apply Over.OverMorphism.ext
    exact ext_of_apply_closedPoint_eq X.hom (Over.w _) (Over.w _) h2

end Langlands.GroupScheme.ProjectiveTorusFixedPoint
