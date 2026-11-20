import Langlands.GroupScheme.Trigonalizable
import Langlands.GroupScheme.Trigonalizable.CoalgebraCriterion
import Langlands.GroupScheme.UnipotentMatrixCriterion.Coordinates

/-! # Stable lines: universal points, epimorphic restriction and coefficient matrices

A stable line is tested by one equation at the universal point. Along a group homomorphism whose
underlying scheme map is an epimorphism, global functions pull back injectively, so stable
lines of a restricted representation are already stable lines of the original one; hence
trigonalizability passes to such targets, and in particular to flat surjective images. For a
corepresented affine group, a stable line is exactly a nonzero solution of
`∑ j, v j • a i j = v i • c` for the universal coefficient matrix `a`, so trigonalizability is
the coalgebra condition `CoalgebraTrigonalizable.IsMatrixTrigonalizable` of its coordinate
bialgebra.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Matrix

namespace Langlands.GroupScheme

/-- If a matrix equation `M v = c v` holds after an injective ring map, and one coordinate of
`v` is a unit, then `M v` is already a multiple of `v`. -/
theorem exists_mulVec_eq_smul_of_injective {n : Type} [Fintype n] {A A' : Type*}
    [CommRing A] [CommRing A'] (φ : A →+* A') (hφ : Function.Injective φ)
    (M : Matrix n n A) (s : n → A) {i₀ : n} (hs : IsUnit (s i₀)) (c : A')
    (h : M.map φ *ᵥ (φ ∘ s) = c • (φ ∘ s)) : ∃ d : A, M *ᵥ s = d • s := by
  refine ⟨(M *ᵥ s) i₀ * ↑hs.unit⁻¹, funext fun i => hφ ?_⟩
  have hM : ∀ j, φ ((M *ᵥ s) j) = c * φ (s j) := fun j => by
    rw [RingHom.map_mulVec, h]
    rfl
  have hu : φ (↑hs.unit⁻¹ : A) * φ (s i₀) = 1 := by
    rw [← map_mul, ← map_one φ]
    congr 1
    exact hs.val_inv_mul
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_mul, hM, hM]
  calc c * φ (s i) = c * (φ (↑hs.unit⁻¹ : A) * φ (s i₀)) * φ (s i) := by rw [hu, mul_one]
    _ = c * φ (s i₀) * φ (↑hs.unit⁻¹ : A) * φ (s i) := by ring

namespace MatrixRepresentation

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)} {n : Type} [Fintype n]
  [DecidableEq n]

/-- One universal-point equation tests a stable line on every scheme. -/
theorem isStableLine_iff_universal (ρ : MatrixRepresentation G n) (v : n → R) :
    ρ.IsStableLine v ↔ ∃ c : Γ(G.X.left, ⊤),
      (ρ.pointMatrix G.X (𝟙 G.X) : Matrix n n Γ(G.X.left, ⊤)) *ᵥ
        (fun i => scalarMap G.X (v i)) = c • fun i => scalarMap G.X (v i) := by
  constructor
  · exact fun h => h G.X (𝟙 G.X)
  · rintro ⟨c, h⟩ T g
    refine ⟨g.left.appTop c, ?_⟩
    have hmat := ρ.pointMatrix_naturality g (𝟙 G.X)
    rw [Category.comp_id] at hmat
    rw [hmat]
    funext i
    have hi := congrArg (fun w => g.left.appTop.hom (w i)) h
    rw [g.left.appTop.hom.map_mulVec] at hi
    change (((ρ.pointMatrix G.X (𝟙 G.X) : Matrix n n Γ(G.X.left, ⊤)).map
      g.left.appTop.hom) *ᵥ (fun j => scalarMap T (v j))) i = _
    simpa only [Function.comp_def, scalarMap_naturality, Pi.smul_apply, smul_eq_mul,
      map_mul] using hi

/-- Restricting to a scheme-epimorphic source changes no stable line whose coordinate vector
has a unit coordinate. -/
theorem isStableLine_restrict_iff (ρ : MatrixRepresentation G n) (q : H ⟶ G)
    [Epi q.hom.hom.left] {v : n → R} {i₀ : n} (hv : IsUnit (v i₀)) :
    (ρ.restrict q).IsStableLine v ↔ ρ.IsStableLine v := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h H.X (𝟙 H.X)
    rw [pointMatrix_restrict, Category.id_comp] at hc
    have hmat := ρ.pointMatrix_naturality q.hom.hom (𝟙 G.X)
    rw [Category.comp_id] at hmat
    rw [hmat] at hc
    apply (ρ.isStableLine_iff_universal v).2
    apply exists_mulVec_eq_smul_of_injective q.hom.hom.left.appTop.hom
      (Langlands.Scheme.UnitCocycleDescent.appTop_injective_of_epi q.hom.hom.left) _ _
      (hv.map (scalarMap G.X)) c
    have hs : (q.hom.hom.left.appTop.hom ∘ fun i => scalarMap G.X (v i)) =
        fun i => scalarMap H.X (v i) := by
      funext i
      exact scalarMap_naturality q.hom.hom (v i)
    rw [hs]
    exact hc
  · intro h T x
    rw [pointMatrix_restrict]
    exact h T (x ≫ q.hom.hom)

end MatrixRepresentation

section Field

variable {k : Type u} [Field k] {G H H' : GroupScheme (Spec (CommRingCat.of k))}

/-- Trigonalizability descends along any group homomorphism whose underlying scheme map is an
epimorphism. -/
theorem IsTrigonalizable.of_epi (hH : IsTrigonalizable H) (q : H ⟶ G)
    [Epi q.hom.hom.left] : IsTrigonalizable G := by
  intro n _ _ _ ρ
  obtain ⟨v, hv, hst⟩ := hH n (ρ.restrict q)
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  exact ⟨v, hv, (ρ.isStableLine_restrict_iff q (v := v) (i₀ := i₀) hi₀.isUnit).1 hst⟩

/-- Flat surjective homomorphisms preserve trigonalizability. -/
theorem IsTrigonalizable.of_flat_surjective (hH : IsTrigonalizable H) (q : H ⟶ G)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left] : IsTrigonalizable G := by
  let := Flat.epi_of_flat_of_surjective q.hom.hom.left
  exact hH.of_epi q

/-- Trigonalizability is invariant under group-scheme isomorphism. -/
theorem IsTrigonalizable.of_iso (e : H ≅ H') (h : IsTrigonalizable H') :
    IsTrigonalizable H := by
  intro n _ _ _ ρ
  obtain ⟨v, hv, hst⟩ := h n (ρ.restrict e.inv)
  refine ⟨v, hv, ?_⟩
  intro T g
  have hg := hst T (g ≫ e.hom.hom.hom)
  simpa only [MatrixRepresentation.pointMatrix_restrict, Category.assoc,
    ← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom, Category.comp_id] using hg

end Field

namespace TrigonalizableMatrixCriterion

open UnipotentMatrixCriterion

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {n : Type} [Fintype n] [DecidableEq n]

/-- For a corepresented group, a stable line is a coordinate vector `v` with
`∑ j, v j • a i j = v i • c` for the universal coefficient matrix `a` and some `c ∈ B`. -/
theorem isStableLine_iff
    (ρ : MatrixRepresentation (Corepresented.groupScheme F e) n) (v : n → R) :
    ρ.IsStableLine v ↔
      ∃ c : B, ∀ i, ∑ j, v j • coefficientMatrix e ρ i j = v i • c := by
  rw [ρ.isStableLine_iff_universal v, coefficientMatrix_eq_affineMatrix]
  change (∃ c : Γ(((algSpec R).obj (op B)).left, ⊤),
    (ρ.pointMatrix ((algSpec R).obj (op B)) (𝟙 _) :
      Matrix n n Γ(((algSpec R).obj (op B)).left, ⊤)) *ᵥ
        (fun i => scalarMap ((algSpec R).obj (op B)) (v i)) =
          c • fun i => scalarMap ((algSpec R).obj (op B)) (v i)) ↔ _
  let q : B →+* Γ(((algSpec R).obj (op B)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  have hq : Function.Bijective q :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).inv
  have hs (r : R) : scalarMap ((algSpec R).obj (op B)) r = q (algebraMap R B r) :=
    scalarMap_affine B r
  rw [ρ.pointMatrix_eq_affineMatrix B (𝟙 _),
    Corepresented.affineSectionsIso_inv_ringHom]
  let a : Matrix n n B := ρ.affineMatrix B (𝟙 _)
  change (∃ c : Γ(((algSpec R).obj (op B)).left, ⊤),
    (fun i => ∑ j, q (a i j) * scalarMap ((algSpec R).obj (op B)) (v j)) =
      c • fun i => scalarMap ((algSpec R).obj (op B)) (v i)) ↔
        ∃ c : B, ∀ i, ∑ j, v j • a i j = v i • c
  simp only [funext_iff, hs, Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨c, h⟩
    obtain ⟨c, rfl⟩ := hq.2 c
    refine ⟨c, fun i => hq.1 ?_⟩
    simp only [Algebra.smul_def, map_sum, map_mul]
    calc
      ∑ j, q (algebraMap R B (v j)) * q (a i j) =
          ∑ j, q (a i j) * q (algebraMap R B (v j)) :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = q c * q (algebraMap R B (v i)) := h i
      _ = q (algebraMap R B (v i)) * q c := mul_comm _ _
  · rintro ⟨c, h⟩
    refine ⟨q c, fun i => ?_⟩
    have hi := congrArg q (h i)
    simp only [Algebra.smul_def, map_sum, map_mul] at hi
    calc
      ∑ j, q (a i j) * q (algebraMap R B (v j)) =
          ∑ j, q (algebraMap R B (v j)) * q (a i j) :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = q (algebraMap R B (v i)) * q c := hi
      _ = q c * q (algebraMap R B (v i)) := mul_comm _ _

/-- Trigonalizability of a corepresented group over a field is the coefficient-matrix
stable-line condition for its coordinate bialgebra. -/
theorem isTrigonalizable_iff_isMatrixTrigonalizable (k : Type u) [Field k]
    (F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u})
    (B : CommAlgCat.{u} (CommRingCat.of k))
    (e : (F ⋙ forget GrpCat).CorepresentableBy B) :
    letI := AffineLinearEmbedding.bialgebra e
    IsTrigonalizable (Corepresented.groupScheme F e) ↔
      CoalgebraTrigonalizable.IsMatrixTrigonalizable k B := by
  let := AffineLinearEmbedding.bialgebra e
  constructor
  · intro h N hN a ha
    let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    let ρ : MatrixRepresentation (Corepresented.groupScheme F e) (Fin N) :=
      Corepresented.groupSchemeMap e (GeneralLinear.corepresentableBy (Fin N) (CommRingCat.of k))
        (Corepresented.LinearEmbedding.toGL e a ha.1 ha.2)
    obtain ⟨v, hv, hst⟩ := h (Fin N) ρ
    refine ⟨v, hv, ?_⟩
    have hf := (isStableLine_iff e ρ v).mp hst
    have hc : coefficientMatrix e ρ = a := coefficientMatrix_toGL e a ha.1 ha.2
    rwa [hc] at hf
  · intro h n _ _ _ ρ
    let f : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm
    let a : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) B :=
      fun i j => coefficientMatrix e ρ (f i) (f j)
    have ha : CoalgebraUnipotence.IsCoefficientMatrix (k := k) a := by
      constructor
      · intro i j
        change AffineLinearEmbedding.comul e (coefficientMatrix e ρ (f i) (f j)) =
          ∑ l, coefficientMatrix e ρ (f i) (f l) ⊗ₜ[k] coefficientMatrix e ρ (f l) (f j)
        rw [coefficientMatrix_comul]
        exact (f.sum_comp fun l =>
          coefficientMatrix e ρ (f i) l ⊗ₜ[k] coefficientMatrix e ρ l (f j)).symm
      · intro i j
        change AffineLinearEmbedding.counit e (coefficientMatrix e ρ (f i) (f j)) =
          (1 : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) k) i j
        rw [coefficientMatrix_counit]
        simp only [Matrix.one_apply, f.injective.eq_iff]
    obtain ⟨v, hv, c, hst⟩ := h (Fintype.card n) Fintype.card_pos a ha
    refine ⟨fun i => v (f.symm i), ?_, (isStableLine_iff e ρ _).mpr ⟨c, ?_⟩⟩
    · intro hz
      apply hv
      funext i
      have hi := congrFun hz (f i)
      simpa only [Equiv.symm_apply_apply, Pi.zero_apply] using hi
    · intro i
      have hi := hst (f.symm i)
      change (∑ j, v j • coefficientMatrix e ρ (f (f.symm i)) (f j)) =
        v (f.symm i) • c at hi
      rw [Equiv.apply_symm_apply] at hi
      calc
        ∑ j, v (f.symm j) • coefficientMatrix e ρ i j =
            ∑ j, v j • coefficientMatrix e ρ i (f j) := by
          simpa only [Equiv.symm_apply_apply] using
            (f.sum_comp fun j => v (f.symm j) • coefficientMatrix e ρ i j).symm
        _ = _ := hi

end TrigonalizableMatrixCriterion

end Langlands.GroupScheme
