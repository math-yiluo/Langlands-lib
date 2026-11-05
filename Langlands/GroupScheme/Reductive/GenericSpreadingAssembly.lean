import Langlands.GroupScheme.Reductive.GenericFiberGeometry
import Langlands.GroupScheme.Reductive.GenericSpreadingStatement
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof

/-! # Actual-fibre reductions for generic reductivity spreading -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Points whose actual residue-field fibres are connected reductive. -/
def residueReductiveLocus {S : Scheme.{u}} (G : GroupScheme S) : Set S :=
  {s | IsConnectedReductive ((baseChange (S.fromSpecResidueField s)).obj G)}

/-- Reductivity of a specified field-valued pullback descends to the
actual residue-field fibre at its image. -/
theorem residueReductive_of_fieldReductive {S : Scheme.{u}} (G : GroupScheme S)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S)
    (h : IsConnectedReductive ((baseChange b).obj G)) :
    IsConnectedReductive
      ((baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj G) := by
  let : Algebra (S.residueField (b (IsLocalRing.closedPoint k))) k :=
    (fieldPointResidueMap b).hom.toAlgebra
  have h' : IsConnectedReductive
      ((baseChange (Spec.map (fieldPointResidueMap b))).obj
        ((baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj G)) :=
    h.of_iso (fieldPointFiberIso G b).symm
  exact IsConnectedReductive.of_fieldExtension
    (k := S.residueField (b (IsLocalRing.closedPoint k))) (K := k) h'

/-- A field-valued pullback is connected reductive if and only if its
actual residue-field fibre is connected reductive. -/
theorem fieldReductive_iff_residueReductive {S : Scheme.{u}} (G : GroupScheme S)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsConnectedReductive ((baseChange b).obj G) ↔
      IsConnectedReductive
        ((baseChange (S.fromSpecResidueField (b (IsLocalRing.closedPoint k)))).obj G) := by
  constructor
  · exact residueReductive_of_fieldReductive G b
  · intro h
    exact fieldReductive_of_residueReductive G {b (IsLocalRing.closedPoint k)}
      (by
        intro s hs
        have hs' : s = b (IsLocalRing.closedPoint k) := hs
        subst s
        exact h) b
      (Set.mem_singleton _)

/-- The closed point of every supplied fraction field maps to the
scheme-theoretic generic point of the actual domain spectrum. -/
theorem fractionFieldPoint_eq_genericPoint (R K : Type u)
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :
    (Spec.algebraMap R K) (IsLocalRing.closedPoint K) =
      genericPoint (Spec (CommRingCat.of R)) := by
  rw [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R K) (IsLocalRing.maximalIdeal K) = ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot,
    Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]

/-- Reductivity of the supplied fraction-field pullback implies
reductivity of the actual scheme-theoretic generic residue-field fibre. -/
theorem genericResidueReductive_of_fractionFieldReductive (R K : Type u)
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of R)))
    (h : IsConnectedReductive ((baseChange (Spec.algebraMap R K)).obj G)) :
    IsConnectedReductive ((baseChange
      ((Spec (CommRingCat.of R)).fromSpecResidueField
        (genericPoint (Spec (CommRingCat.of R))))).obj G) := by
  have h' := residueReductive_of_fieldReductive G (Spec.algebraMap R K) h
  rwa [fractionFieldPoint_eq_genericPoint R K] at h'

/-- Residue-fibre reductivity supplies the radical predicate on the
single actual geometric pullback used by `geometricFiber`. -/
theorem geometricRadical_of_residueReductive {S : Scheme.{u}} (G : GroupScheme S)
    (s : S)
    (h : IsConnectedReductive ((baseChange (S.fromSpecResidueField s)).obj G)) :
    HasTrivialUnipotentRadical (geometricFiber G s) :=
  HasTrivialUnipotentRadical.of_iso
    (baseChangeCompIso (S.fromSpecResidueField s)
      (toAlgebraicClosure (S.residueField s)) G)
    h.hasTrivialGeometricUnipotentRadical

/-- Connectedness of a residue fibre and radical triviality of its actual
geometric fibre imply connected reductivity of that residue fibre. -/
theorem residueReductive_of_connected_geometricRadical {S : Scheme.{u}}
    (G : GroupScheme S) (hsm : Smooth G.X.hom) (haff : IsAffineHom G.X.hom)
    (s : S)
    (hc : ConnectedSpace ((baseChange (S.fromSpecResidueField s)).obj G).X.left)
    (hr : HasTrivialUnipotentRadical (geometricFiber G s)) :
    IsConnectedReductive ((baseChange (S.fromSpecResidueField s)).obj G) := by
  let : Smooth G.X.hom := hsm
  let : IsAffineHom G.X.hom := haff
  refine ⟨?_, ?_, hc, ?_⟩
  · change Smooth (pullback.snd G.X.hom (S.fromSpecResidueField s))
    infer_instance
  · change IsAffineHom (pullback.snd G.X.hom (S.fromSpecResidueField s))
    infer_instance
  · exact HasTrivialUnipotentRadical.of_iso
      (baseChangeCompIso (S.fromSpecResidueField s)
        (toAlgebraicClosure (S.residueField s)) G).symm hr

end Langlands.GroupScheme
