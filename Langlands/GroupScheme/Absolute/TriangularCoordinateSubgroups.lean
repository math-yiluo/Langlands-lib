import Langlands.GroupScheme.Absolute.TriangularCoordinateFiltration
import Langlands.GroupScheme.CorepresentedClosedSubgroup
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction

/-! # Actual closed subgroup schemes for the refined triangular filtration -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TriangularLayer

variable {A : Type*} [CommRing A] {N : ℕ}

/-- The matrix positions fixed to their identity values in a refined term. -/
def refinedPosition (a b : ℕ) (i j : Fin N) : Prop :=
  (j : ℕ) ≤ i + a ∨ (j : ℕ) = i + a + 1 ∧ (i : ℕ) < b

/-- Each refined term is cut out by explicit matrix-entry equations. -/
theorem mem_refinedW_iff_entries (a b : ℕ) (g : GL (Fin N) A) :
    g ∈ refinedW A N a b ↔
      ∀ i j, refinedPosition a b i j →
        (g : Matrix (Fin N) (Fin N) A) i j = (1 : Matrix (Fin N) (Fin N) A) i j := by
  constructor
  · rintro ⟨hg, hz⟩ i j (hij | ⟨hij, hi⟩)
    · exact sub_eq_zero.mp (mem_W.1 hg i j hij)
    · have h := hz i j hi
      rw [layer_apply, ite_eq_left hij, Matrix.sub_apply, sub_eq_zero] at h
      exact h
  · intro h
    constructor
    · rw [mem_W]
      intro i j hij
      rw [Matrix.sub_apply, h i j (Or.inl hij), sub_self]
    · intro i j hi
      rw [layer_apply]
      split_ifs with hij
      · rw [Matrix.sub_apply, h i j (Or.inr ⟨hij, hi⟩), sub_self]
      · rfl

variable (N) (R : CommRingCat.{u})

/-- The ideal imposing the refined matrix-entry equations. -/
def refinedIdeal (a b : ℕ) : Ideal (GeneralLinear.CoordinateRing (Fin N) R) :=
  GeneralLinear.entryIdeal (Fin N) R (refinedPosition a b)
    (fun i j => (1 : Matrix (Fin N) (Fin N) R) i j)

/-- The refined unitriangular subgroup is represented by the quotient
coordinate ring, without any field or reducedness assumption. -/
theorem isCutOutBy_refinedW (a b : ℕ) :
    Corepresented.IsCutOutBy (GeneralLinear.corepresentableBy (Fin N) R)
      (fun A => refinedW A N a b) (refinedIdeal N R a b) := by
  apply GeneralLinear.isCutOutBy_entryIdeal
  intro A g
  change g ∈ refinedW A N a b ↔ ∀ i j, refinedPosition a b i j →
    (g : Matrix (Fin N) (Fin N) A) i j =
      algebraMap R A ((1 : Matrix (Fin N) (Fin N) R) i j)
  rw [mem_refinedW_iff_entries]
  have h1 (i j : Fin N) :
      algebraMap R A ((1 : Matrix (Fin N) (Fin N) R) i j) =
        (1 : Matrix (Fin N) (Fin N) A) i j :=
    congrFun (congrFun (map_one (algebraMap R A).mapMatrix) i) j
  simp only [h1]

/-- The actual closed affine group scheme of a refined filtration term. -/
abbrev refinedScheme (a b : ℕ) : GroupScheme (Spec R) :=
  Corepresented.cutGroupScheme (isCutOutBy_refinedW N R a b)

/-- The actual closed immersion of a refined term into the general linear group. -/
abbrev refinedHom (a b : ℕ) :
    refinedScheme N R a b ⟶ GeneralLinear.groupScheme (Fin N) R :=
  Corepresented.cutHom (isCutOutBy_refinedW N R a b)

theorem isClosedSubgroup_refinedHom (a b : ℕ) :
    IsClosedSubgroup (refinedHom N R a b) :=
  Corepresented.isClosedSubgroup_cutHom _

/-- The corresponding subgroup functor on all schemes over the base. -/
abbrev refinedFunctor (a b : ℕ) :
    SubgroupFunctor (GeneralLinear.groupScheme (Fin N) R) :=
  Corepresented.cutSubgroupFunctor (isCutOutBy_refinedW N R a b)

theorem range_refinedHom (a b : ℕ) :
    SubgroupFunctor.range (refinedHom N R a b) = refinedFunctor N R a b :=
  Corepresented.range_cutHom _

theorem mem_refinedFunctor {a b : ℕ} {T : Over (Spec R)}
    (x : T ⟶ (GeneralLinear.groupScheme (Fin N) R).X) :
    x ∈ (refinedFunctor N R a b).carrier T ↔
      GeneralLinear.pointsEquiv (Fin N) R T x ∈ refinedW Γ(T.left, ⊤) N a b :=
  Iff.rfl

variable {N R} {H : GroupScheme (Spec R)}

/-- Pull the full refined term back along an actual matrix representation.
No reduction or identity component is taken. -/
abbrev filtrationScheme (ρ : MatrixRepresentation H (Fin N)) (a b : ℕ) :
    GroupScheme (Spec R) :=
  SubgroupPreimage.groupScheme ρ (refinedHom N R a b)

/-- The closed inclusion of the full inverse-image term into the original group. -/
abbrev filtrationHom (ρ : MatrixRepresentation H (Fin N)) (a b : ℕ) :
    filtrationScheme ρ a b ⟶ H :=
  SubgroupPreimage.inclusion ρ (refinedHom N R a b)

theorem isClosedSubgroup_filtrationHom (ρ : MatrixRepresentation H (Fin N)) (a b : ℕ) :
    IsClosedSubgroup (filtrationHom ρ a b) :=
  SubgroupPreimage.isClosedSubgroup _ _ (isClosedSubgroup_refinedHom N R a b)

/-- All test schemes see exactly the original matrix equations on the
scheme-theoretic inverse image. -/
theorem mem_range_filtrationHom (ρ : MatrixRepresentation H (Fin N)) (a b : ℕ)
    {T : Over (Spec R)} (x : T ⟶ H.X) :
    x ∈ (SubgroupFunctor.range (filtrationHom ρ a b)).carrier T ↔
      ρ.pointMatrix T x ∈ refinedW Γ(T.left, ⊤) N a b := by
  rw [SubgroupPreimage.range_inclusion, range_refinedHom,
    SubgroupFunctor.mem_comap, mem_refinedFunctor]
  rfl

theorem isAffineHom_filtrationScheme (ρ : MatrixRepresentation H (Fin N)) (a b : ℕ)
    [IsAffineHom H.X.hom] : IsAffineHom (filtrationScheme ρ a b).X.hom :=
  SubgroupPreimage.isAffineHom _ _ (isClosedSubgroup_refinedHom N R a b)

theorem locallyOfFiniteType_filtrationScheme
    (ρ : MatrixRepresentation H (Fin N)) (a b : ℕ)
    [LocallyOfFiniteType H.X.hom] :
    LocallyOfFiniteType (filtrationScheme ρ a b).X.hom := by
  have : IsClosedImmersion (filtrationHom ρ a b).hom.hom.left :=
    isClosedSubgroup_filtrationHom ρ a b
  rw [← Over.w (filtrationHom ρ a b).hom.hom]
  infer_instance

/-- The inverse-image terms decrease as successive coordinates are killed. -/
theorem filtration_anti (ρ : MatrixRepresentation H (Fin N)) (a : ℕ)
    {b c : ℕ} (hbc : b ≤ c) :
    SubgroupFunctor.range (filtrationHom ρ a c) ≤
      SubgroupFunctor.range (filtrationHom ρ a b) := by
  intro T x hx
  rw [mem_range_filtrationHom] at hx ⊢
  exact refinedW_anti a hbc hx

/-- Normality is proved on every test scheme, provided the original
representation is upper triangular there. -/
theorem isNormal_filtrationHom (ρ : MatrixRepresentation H (Fin N))
    (hρ : ∀ (T : Over (Spec R)) (x : T ⟶ H.X),
      ρ.pointMatrix T x ∈ upper Γ(T.left, ⊤) N) (a b : ℕ) :
    (SubgroupFunctor.range (filtrationHom ρ a b)).IsNormal := by
  intro T g x _ hx
  rw [mem_range_filtrationHom] at hx ⊢
  rw [map_mul, map_mul, map_inv]
  simpa only [inv_inv] using refinedW_conj
    ((upper Γ(T.left, ⊤) N).inv_mem (hρ T g)) hx

/-- An actual homomorphism to the triangular subgroup gives upper triangular
matrices on all test schemes. -/
theorem triangular_pointMatrix_mem_upper
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) R
      (fun i => -(i.val : ℤ))) (T : Over (Spec R)) (x : T ⟶ H.X) :
    MatrixRepresentation.pointMatrix
      (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) T x ∈
      upper Γ(T.left, ⊤) N := by
  have h := ((GeneralLinear.isRepresentedBy_blockParabolic (Fin N) R
    (fun i => -(i.val : ℤ))).pointsEquiv T (x ≫ j.hom.hom)).property
  exact h

/-- The full refined inverse-image terms of every triangular homomorphism
are normal subgroup functors of its source. -/
theorem isNormal_triangular_filtration
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) R
      (fun i => -(i.val : ℤ))) (a b : ℕ) :
    (SubgroupFunctor.range (filtrationHom
      (j ≫ GeneralLinear.blockParabolicHom (Fin N) R _) a b)).IsNormal :=
  isNormal_filtrationHom _ (triangular_pointMatrix_mem_upper j) a b

/-- Killing all rows advances to the next superdiagonal, on the full
inverse-image subgroup functors. -/
theorem filtration_top (ρ : MatrixRepresentation H (Fin N)) (a : ℕ) :
    SubgroupFunctor.range (filtrationHom ρ a N) =
      SubgroupFunctor.range (filtrationHom ρ (a + 1) 0) := by
  ext T x
  rw [mem_range_filtrationHom, mem_range_filtrationHom,
    refinedW_top, refinedW_zero]

/-- A faithful representation makes the last filtration term the full
trivial subgroup functor, including on nonreduced test schemes. -/
theorem filtration_eq_bot (ρ : MatrixRepresentation H (Fin N))
    [Mono ρ.hom.hom] :
    SubgroupFunctor.range (filtrationHom ρ N 0) = ⊥ := by
  ext T x
  rw [mem_range_filtrationHom, refinedW_zero, SubgroupFunctor.bot_carrier,
    Subgroup.mem_bot]
  constructor
  · intro hx
    apply (cancel_mono ρ.hom.hom).mp
    apply (GeneralLinear.pointsEquiv (Fin N) R T).injective
    rw [MonObj.one_comp, map_one]
    exact eq_one_of_mem_W_top hx
  · rintro rfl
    rw [map_one]
    exact (W Γ(T.left, ⊤) N N).one_mem

end Langlands.GroupScheme.TriangularLayer
