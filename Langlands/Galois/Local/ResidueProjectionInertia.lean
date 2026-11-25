import Langlands.Galois.Local.AbsoluteProof

/-!
# The residue projection of a separable closure: the residue homomorphism and inertia

For a nonarchimedean local field `K` of either characteristic and a separable
closure `Ω` of `K`, write `ρ = SepClosed.absoluteResidueHom K Ω` for the residue
homomorphism from `Ω ≃ₐ[K] Ω` to `Field.absoluteGaloisGroup 𝓀[K]` and
`I = SepClosed.absoluteInertia K Ω` for inertia. This file proves:

* `ρ σ` acts on residues of integers of `Ω` as `σ` does (`absoluteResidueHom_residue`), and
  compatibly with restriction to normal intermediate fields
  (`absoluteResidueHom_restrictNormal`);
* the conjugation `SepClosed.residueTransport K Ω` is a homeomorphism
  (`residueTransportEquiv`), and `ρ` is an open map (`isOpenMap_absoluteResidueHom`);
* `I` is the set of automorphisms acting trivially on residues, the preimage of Mathlib's
  inertia subgroup of the integers of `Ω` under the decomposition map, and is closed,
  compact, totally disconnected and Hausdorff.

Continuity, surjectivity and the kernel of `ρ` are the Library's
`SepClosed.absoluteResidueHom_continuous`, `SepClosed.absoluteResidueHom_surjective` and
`SepClosed.absoluteResidueHom_ker` (`Galois/Local/AbsoluteProof.lean`); normality of `I`
is the instance `SepClosed.absoluteInertia_normal` (`Galois/Local/AbsoluteDefinitions.lean`).
-/

noncomputable section

open ValuativeRel IsLocalRing

namespace Langlands.LocalGalois.SepClosed

universe uK uΩ

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local instance rpInertiaIsAlgebraic : Algebra.IsAlgebraic K Ω :=
    Algebra.IsSeparable.isAlgebraic K Ω
local instance rpInertiaNormedField : NontriviallyNormedField K := localNormedField K
local instance rpInertiaUltrametric : IsUltrametricDist K := localNormedField_ultrametric K
local instance rpInertiaComplete : CompleteSpace K := localNormedField_complete K
local instance rpInertiaResidueFinite : Finite (ResidueField (baseIntegers K)) :=
    localResidue_finite K

/-- Through the comparison `residueClosureEquiv K Ω`, the residue automorphism
`absoluteResidueHom K Ω σ` sends the residue of an integer `x` of `Ω` to the residue of
`σ x`. -/
theorem absoluteResidueHom_residue (σ : Ω ≃ₐ[K] Ω) (x : closureIntegers K Ω) :
    haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
    (AlgEquiv.toAlgHom (absoluteResidueHom K Ω σ))
        (residueClosureEquiv K Ω (residue _ x)) =
      residueClosureEquiv K Ω (residue _ (integerAut K Ω σ x)) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  change residueClosureEquiv K Ω
      (residueHom K Ω σ
        ((residueClosureEquiv K Ω).symm (residueClosureEquiv K Ω (residue _ x)))) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

/-- The conjugation `residueTransport K Ω` from the Galois group of the residue extension of
`Ω/K` to `Field.absoluteGaloisGroup 𝓀[K]`, as an isomorphism of topological groups. -/
def residueTransportEquiv :
    Gal(ResidueField (closureIntegers K Ω)/ResidueField (baseIntegers K)) ≃ₜ*
      Field.absoluteGaloisGroup 𝓀[K] := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  let := residue_isAlgClosure K Ω
  let : IsAlgClosed (ResidueField (closureIntegers K Ω)) :=
    (residue_isAlgClosure K Ω).isAlgClosed
  let : IsGalois (ResidueField (baseIntegers K)) (ResidueField (closureIntegers K Ω)) := ⟨⟩
  let : T2Space (Field.absoluteGaloisGroup 𝓀[K]) :=
    inferInstanceAs (T2Space Gal(AlgebraicClosure 𝓀[K]/𝓀[K]))
  exact
    { toMulEquiv := residueTransport K Ω
      continuous_toFun := residueTransport_continuous K Ω
      continuous_invFun :=
        (residueTransport_continuous K Ω).continuous_symm_of_equiv_compact_to_t2 }

/-- `residueTransportEquiv K Ω` is `residueTransport K Ω` as a map. -/
theorem residueTransportEquiv_apply
    (τ : Gal(ResidueField (closureIntegers K Ω)/ResidueField (baseIntegers K))) :
    haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
    residueTransportEquiv K Ω τ = residueTransport K Ω τ :=
  rfl

/-- The residue homomorphism `absoluteResidueHom K Ω` of a separable closure is an open
map. -/
theorem isOpenMap_absoluteResidueHom :
    haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
    IsOpenMap (absoluteResidueHom K Ω) :=
  (residueTransportEquiv K Ω).toHomeomorph.isOpenMap.comp (residueHom_isOpenMap K Ω)

/-- An automorphism of `Ω` over `K` lies in the inertia subgroup `absoluteInertia K Ω` exactly
when it acts trivially on the residues of all integers of `Ω`. -/
theorem mem_absoluteInertia_iff (σ : Ω ≃ₐ[K] Ω) :
    σ ∈ absoluteInertia K Ω ↔ ∀ x : closureIntegers K Ω,
      residue _ (integerAut K Ω σ x) = residue _ x :=
  mem_inertia_iff K Ω σ

/-- The inertia subgroup `absoluteInertia K Ω` is the preimage, under the decomposition map
`decompositionHom K Ω`, of Mathlib's inertia subgroup of the valuation subring
`closureIntegers K Ω`. -/
theorem absoluteInertia_eq_comap_decompositionHom :
    absoluteInertia K Ω =
      ((closureIntegers K Ω).inertiaSubgroup K).comap (decompositionHom K Ω) :=
  inertia_eq_comap_valuationSubring K Ω

/-- The inertia subgroup `absoluteInertia K Ω` is closed in the Krull topology. -/
theorem isClosed_absoluteInertia : IsClosed (absoluteInertia K Ω : Set (Ω ≃ₐ[K] Ω)) :=
  inertia_isClosed K Ω

/-- The inertia subgroup `absoluteInertia K Ω` is compact in the subspace topology. -/
instance compactSpace_absoluteInertia : CompactSpace (absoluteInertia K Ω) :=
  inertia_compactSpace K Ω

/-- The inertia subgroup `absoluteInertia K Ω` is totally disconnected in the subspace
topology. -/
theorem totallyDisconnectedSpace_absoluteInertia :
    TotallyDisconnectedSpace (absoluteInertia K Ω) :=
  inertia_totallyDisconnectedSpace K Ω

/-- The inertia subgroup `absoluteInertia K Ω` is Hausdorff in the subspace topology. -/
theorem t2Space_absoluteInertia : T2Space (absoluteInertia K Ω) :=
  inferInstanceAs (T2Space (inertia K Ω))

/-- Reduction commutes with restriction to a normal intermediate field `E` of `Ω/K`: through
`residueInclusion K Ω E` and the comparison `residueClosureEquiv K Ω`, the residue
automorphism `absoluteResidueHom K Ω σ` acts on residues of integers of `E` as the residue
automorphism `residueHom K E` of `σ.restrictNormal E`. -/
theorem absoluteResidueHom_restrictNormal (E : IntermediateField K Ω) [Normal K E]
    (σ : Ω ≃ₐ[K] Ω) (y : ResidueField (extensionIntegers K E)) :
    haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
    (AlgEquiv.toAlgHom (absoluteResidueHom K Ω σ))
        (residueClosureEquiv K Ω (residueInclusion K Ω E y)) =
      residueClosureEquiv K Ω
        (residueInclusion K Ω E (residueHom K E (σ.restrictNormal E) y)) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  change residueClosureEquiv K Ω
      (residueHom K Ω σ ((residueClosureEquiv K Ω).symm (residueClosureEquiv K Ω _))) = _
  rw [RingEquiv.symm_apply_apply]
  exact congrArg (residueClosureEquiv K Ω) (residueHom_restrict K Ω E σ y).symm

end Langlands.LocalGalois.SepClosed
