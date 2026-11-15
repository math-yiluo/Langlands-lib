import Langlands.Geometry.Building.Kottwitz.CentralTorusExactnessStatement
import Langlands.Geometry.Building.Kottwitz.FundamentalInertiaMapProof
import Langlands.GroupScheme.AlgebraicFundamentalGroupCentralTorusProof
import Langlands.GroupScheme.AlgebraicFundamentalGroupMapProof

/-! # Right exactness of inertia coinvariants for a central torus quotient -/

noncomputable section
universe u v w₁ w₂ w₃
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Representation.Coinvariants

variable {R : Type u} {Γ : Type v} [CommRing R] [Monoid Γ]
  {A : Type w₁} {B : Type w₂} {C : Type w₃} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {ρA : Representation R Γ A} {ρB : Representation R Γ B} {ρC : Representation R Γ C}

/-- Right exactness of coinvariants: if `A → B → C → 0` is exact and the second
map is equivariant, then any descents of the two maps to coinvariants form a
right exact sequence. -/
theorem rightExact_of_descent (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hg : ∀ (g' : Γ) (y : B), g (ρB g' y) = ρC g' (g y))
    (mf : Coinvariants ρA →ₗ[R] Coinvariants ρB)
    (hmf : ∀ z, mf (mk ρA z) = mk ρB (f z))
    (mg : Coinvariants ρB →ₗ[R] Coinvariants ρC)
    (hmg : ∀ y, mg (mk ρB y) = mk ρC (g y))
    (hsurj : Function.Surjective g) (hexact : LinearMap.ker g = LinearMap.range f) :
    Function.Surjective mg ∧ LinearMap.ker mg = LinearMap.range mf := by
  refine ⟨fun c => ?_, le_antisymm ?_ ?_⟩
  · obtain ⟨c, rfl⟩ := mk_surjective ρC c
    obtain ⟨b, rfl⟩ := hsurj c
    exact ⟨mk ρB b, hmg b⟩
  · intro y hy
    obtain ⟨b, rfl⟩ := mk_surjective ρB y
    rw [LinearMap.mem_ker, hmg, mk_eq_zero] at hy
    have hle : Coinvariants.ker ρC ≤ (Coinvariants.ker ρB).map g := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨g', c⟩, rfl⟩
      obtain ⟨b', rfl⟩ := hsurj c
      exact ⟨ρB g' b' - b', sub_mem_ker g' b', by simp [hg]⟩
    obtain ⟨b', hb', hgb'⟩ := hle hy
    have hdiff : b - b' ∈ LinearMap.ker g := by
      rw [LinearMap.mem_ker, map_sub, hgb', sub_self]
    rw [hexact] at hdiff
    obtain ⟨z, hz⟩ := hdiff
    refine ⟨mk ρA z, ?_⟩
    rw [hmf, hz, mk_eq_iff, sub_sub_cancel_left]
    exact neg_mem hb'
  · rintro _ ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := mk_surjective ρA y
    have hz : f z ∈ LinearMap.ker g := hexact ▸ LinearMap.mem_range_self f z
    rw [LinearMap.mem_ker] at hz ⊢
    rw [hmf, hmg, hz, map_zero]

end Representation.Coinvariants

namespace Langlands.Geometry.Building.Kottwitz

/-- **Right exactness of inertia coinvariants for a central torus quotient**
(Kaletha–Prasad, proofs of Lemma 11.5.1 and Proposition 11.5.3). If `Z` is a
closed central torus of the connected reductive group `H` and `p : H → G` is the
fppf quotient by `Z`, then `π₁(Z)_I → π₁(H)_I → π₁(G)_I → 0` is exact for the
selected descended maps. -/
theorem centralTorusInertiaExactness :
    CentralTorusInertiaExactnessStatement.{u} := by
  intro k K E _ _ _ _ _ _ _ _ _ Z hZ H G hH hG i p hcl hcen hq
  obtain ⟨-, hsurj, hexact⟩ :=
    centralTorusFundamentalExactness k E Z hZ H G hH hG i p hcl hcen hq
  have hdesc := (fundamentalInertiaMapStatement k K E).1
  exact Representation.Coinvariants.rightExact_of_descent
    (fundamentalGroupMap k E Z.toGrp H hZ.isConnectedReductive_of_fieldSplitting hH i)
    (fundamentalGroupMap k E H G hH hG p)
    (fun σ y => (algebraicFundamentalGroupMap k E H G hH hG (chosenChoice k H hH)
      (chosenChoice k G hG) p).2.2.1 σ.1 y)
    _ (hdesc Z.toGrp H hZ.isConnectedReductive_of_fieldSplitting hH i).2.1
    _ (hdesc H G hH hG p).2.1
    hsurj hexact.symm

end Langlands.Geometry.Building.Kottwitz
