import Langlands.MathlibBase
import Langlands.Correspondence.HenniartLadicClasses
import WeilConjectures.RepresentationTheory.IntegralModel
import WeilConjectures.Mathlib.RepresentationTheory.Subrepresentation

/-!
# Transport of the ℓ-adic predicates on finite-dimensional representations

For finite-dimensional representations over `E = PadicAlgCl ℓ`, this module proves that the
Library's `IsLadicContinuous` is continuity of all matrix coefficients `g ↦ φ (ρ g v)`, that
`IsLadicContinuous`, `IsLadicDefinedOverFiniteExtension` and irreducibility are invariant under
representation equivalences between arbitrary carrier universes, that a continuous
representation of a compact topological group is defined over a finite extension of `ℚ_ℓ`, and
that every finite-dimensional representation has an equivalent copy in every carrier universe.
-/

noncomputable section

universe uG uH uV uW

open CategoryTheory

namespace Langlands.Henniart.LocalNumerical

section Coefficients

variable (ℓ : ℕ) [Fact ℓ.Prime]

local notation "E" => PadicAlgCl ℓ

/-- The linear map sending a family of coefficients `c i j` to the endomorphism with matrix
`(c i j)` in the basis `b`. -/
def ofCoefficients {V : Type uV} [AddCommGroup V] [Module E V] {n : ℕ}
    (b : Module.Basis (Fin n) E V) : (Fin n → Fin n → E) →ₗ[E] Module.End E V where
  toFun c := ∑ i, ∑ j, c i j • (b.coord j).smulRight (b i)
  map_add' c d := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem ofCoefficients_repr {V : Type uV} [AddCommGroup V] [Module E V] {n : ℕ}
    (b : Module.Basis (Fin n) E V) (f : Module.End E V) :
    ofCoefficients ℓ b (fun i j => b.repr (f (b j)) i) = f := by
  refine b.ext fun k => ?_
  change (∑ i, ∑ j, b.repr (f (b j)) i • (b.coord j).smulRight (b i)) (b k) = f (b k)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
  conv_rhs => rw [← b.sum_repr (f (b k))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- **Continuity in the module topology is continuity of the matrix coefficients.** A map from a
topological space to the endomorphisms of a finite-dimensional `E`-vector space is continuous
for the module topology exactly when every coefficient `g ↦ φ (ρ g v)` is continuous. -/
theorem continuous_moduleTopology_iff {X : Type uG} [TopologicalSpace X] {V : Type uV}
    [AddCommGroup V] [Module E V] [FiniteDimensional E V] (ρ : X → Module.End E V) :
    (letI : TopologicalSpace (Module.End E V) := moduleTopology E (Module.End E V);
      Continuous ρ) ↔ ∀ (φ : Module.Dual E V) (v : V), Continuous fun g => φ (ρ g v) := by
  let : TopologicalSpace (Module.End E V) := moduleTopology E (Module.End E V)
  have : IsModuleTopology E (Module.End E V) := ⟨rfl⟩
  have : ContinuousAdd (Module.End E V) := IsModuleTopology.toContinuousAdd E _
  constructor
  · intro h φ v
    let L : Module.End E V →ₗ[E] E :=
      { toFun f := φ (f v)
        map_add' f g := by simp
        map_smul' a f := by simp }
    exact (IsModuleTopology.continuous_of_linearMap L).comp h
  · intro h
    let b := Module.finBasis E V
    have hc : Continuous fun g => fun i j => b.repr (ρ g (b j)) i :=
      continuous_pi fun i => continuous_pi fun j => h (b.coord i) (b j)
    have := (IsModuleTopology.continuous_of_linearMap (ofCoefficients ℓ b)).comp hc
    refine this.congr fun g => ?_
    exact ofCoefficients_repr ℓ b (ρ g)

/-- `IsLadicContinuous` is the continuity of the matrix coefficients `g ↦ φ (ρ g v)`. -/
theorem isLadicContinuous_iff {G : Type uG} [Group G] [TopologicalSpace G]
    (A : FiniteRepresentation.{0, uG, uV} E G) :
    IsLadicContinuous ℓ A ↔
      ∀ (φ : Module.Dual E A) (v : A), Continuous fun g => φ (A.representation g v) :=
  continuous_moduleTopology_iff ℓ (fun g => A.representation g)

/-- `IsLadicContinuous` is invariant under representation equivalences, between arbitrary
carrier universes. -/
theorem IsLadicContinuous.of_equiv {G : Type uG} [Group G] [TopologicalSpace G]
    {A : FiniteRepresentation.{0, uG, uV} E G} {B : FiniteRepresentation.{0, uG, uW} E G}
    (e : FiniteRepresentation.Equiv A B) (hA : IsLadicContinuous ℓ A) :
    IsLadicContinuous ℓ B := by
  rw [isLadicContinuous_iff] at hA ⊢
  intro φ w
  have h := hA (φ ∘ₗ e.toLinearEquiv.toLinearMap) (e.toLinearEquiv.symm w)
  refine h.congr fun g => ?_
  change φ (e.toLinearEquiv (A.representation g (e.toLinearEquiv.symm w))) =
    φ (B.representation g w)
  congr 1
  have := LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g)
    (e.toLinearEquiv.symm w)
  change e.toLinearEquiv (A.representation g (e.toLinearEquiv.symm w)) =
    B.representation g (e.toLinearEquiv (e.toLinearEquiv.symm w)) at this
  rw [this, LinearEquiv.apply_symm_apply]

/-- `IsLadicDefinedOverFiniteExtension` is invariant under representation equivalences, between
arbitrary carrier universes: the image of a good basis is a good basis. -/
theorem IsLadicDefinedOverFiniteExtension.of_equiv {G : Type uG} [Group G]
    {A : FiniteRepresentation.{0, uG, uV} E G} {B : FiniteRepresentation.{0, uG, uW} E G}
    (e : FiniteRepresentation.Equiv A B) (hA : IsLadicDefinedOverFiniteExtension ℓ A) :
    IsLadicDefinedOverFiniteExtension ℓ B := by
  obtain ⟨L, hL, b, hb⟩ := hA
  have hrank : Module.finrank E A = Module.finrank E B := e.toLinearEquiv.finrank_eq
  refine ⟨L, hL, (b.map e.toLinearEquiv).reindex (finCongr hrank), fun g i j => ?_⟩
  have key : ∀ (k : Fin (Module.finrank E A)),
      B.representation g (e.toLinearEquiv (b k)) =
        e.toLinearEquiv (A.representation g (b k)) := fun k => by
    have := LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) (b k)
    exact this.symm
  rw [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply, Module.Basis.map_apply]
  change b.repr (e.toLinearEquiv.symm
      (B.representation g (e.toLinearEquiv (b ((finCongr hrank).symm j)))))
        ((finCongr hrank).symm i) ∈ L
  rw [key, LinearEquiv.symm_apply_apply]
  exact hb g _ _

/-- Irreducibility is invariant under representation equivalences. -/
theorem isIrreducible_of_equiv {G : Type uG} [Group G]
    {A : FiniteRepresentation.{0, uG, uV} E G} {B : FiniteRepresentation.{0, uG, uW} E G}
    (e : FiniteRepresentation.Equiv A B) (hA : Representation.IsIrreducible A.representation) :
    Representation.IsIrreducible B.representation :=
  (Representation.Equiv.isIrreducible_iff e).1 hA

/-- **Finite models of continuous representations of compact groups.** A continuous
finite-dimensional representation of a compact topological group over `E` is defined over a
finite extension of `ℚ_ℓ`: weil-conjectures's `PadicAlgCl.exists_finiteDimensional_forall_mem`
(a Baire category argument) applied to its matrices in a basis. -/
theorem IsLadicContinuous.isLadicDefinedOverFiniteExtension {G : Type uG} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    {A : FiniteRepresentation.{0, uG, uV} E G} (hA : IsLadicContinuous ℓ A) :
    IsLadicDefinedOverFiniteExtension ℓ A := by
  rw [isLadicContinuous_iff] at hA
  let b := Module.finBasis E A
  let φ : G →* Matrix (Fin (Module.finrank E A)) (Fin (Module.finrank E A)) E :=
    (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp A.representation
  have hφ : ∀ i j, Continuous fun g => φ g i j := fun i j => by
    refine (hA (b.coord i) (b j)).congr fun g => ?_
    change b.repr (A.representation g (b j)) i = LinearMap.toMatrixAlgEquiv b (A.representation g) i j
    rw [LinearMap.toMatrixAlgEquiv_apply]
  obtain ⟨L, hL, hmem⟩ := PadicAlgCl.exists_finiteDimensional_forall_mem ℓ φ hφ
  refine ⟨L, hL, b, fun g i j => ?_⟩
  have := hmem g i j
  change LinearMap.toMatrixAlgEquiv b (A.representation g) i j ∈ L at this
  rwa [LinearMap.toMatrixAlgEquiv_apply] at this

/-- **Change of carrier universe.** Every finite-dimensional representation over `E` is
equivalent to one on a carrier in any prescribed universe, namely on `ULift (Fin n → E)` for
`n` its rank. -/
theorem exists_finiteRepresentation_equiv {G : Type uG} [Group G]
    (A : FiniteRepresentation.{0, uG, uV} E G) :
    ∃ B : FiniteRepresentation.{0, uG, uW} E G, Nonempty (FiniteRepresentation.Equiv A B) := by
  let n := Module.finrank E A
  let e : A ≃ₗ[E] ULift.{uW} (Fin n → E) :=
    (Module.finBasis E A).equivFun.trans ULift.moduleEquiv.symm
  let ρ : Representation E G (ULift.{uW} (Fin n → E)) :=
    { toFun g := e.toLinearMap ∘ₗ A.representation g ∘ₗ e.symm.toLinearMap
      map_one' := LinearMap.ext fun v => by simp
      map_mul' g h := LinearMap.ext fun v => by simp [Module.End.mul_apply] }
  have : Module.Finite E (ULift.{uW} (Fin n → E)) := Module.Finite.equiv e
  refine ⟨FiniteRepresentation.of ρ, ⟨Representation.Equiv.mk e fun g => ?_⟩⟩
  refine LinearMap.ext fun v => ?_
  change e (A.representation g v) = e (A.representation g (e.symm (e v)))
  rw [LinearEquiv.symm_apply_apply]

end Coefficients

end Langlands.Henniart.LocalNumerical
