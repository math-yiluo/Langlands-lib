import Langlands.Sheaf.Equivariant.Godement.Smooth
import Langlands.Cohomology.SmoothSheafCohomology
import Langlands.Cohomology.EquivariantGodementCohomology

/-!
# Exactness and compact acyclicity of the smooth Godement construction

These proposition definitions concern Worker 61's published smooth
equivariant Godement construction: its degree-zero functor, the smooth part
of coinduction of the ordinary Godement sheaf of all stalks, and the cokernel
complex built from it in the abelian category of smooth equivariant sheaves.
The degree-zero functor and every term functor are exact, and on a locally
compact Hausdorff space every term has no compactly supported cohomology in
positive degrees, both for Godement cohomology of the underlying equivariant
sheaf and for the derived compact sections of smooth sheaves. These are the
ordinary-topology analogues of Fact 3 and the acyclicity claim in Harris
1999, section 2, p.304, and of property (ii) of §1.5 and Proposition 1.5.1
in Berkovich's manuscript on étale equivariant sheaves. Exactness and
acyclicity are conclusions; none is supplied as data.
-/

namespace Langlands.Cohomology.SmoothGodement

open CategoryTheory CategoryTheory.Limits Langlands.Sheaf.Equivariant

universe u

/-- The degree-zero smooth Godement functor is additive and exact. -/
def SmoothGodementZeroExactStatement (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
    [HasStableNeighbourhoods G X] : Prop :=
  (Godement.smoothZeroFunctor R G X).Additive ∧
    PreservesFiniteLimits (Godement.smoothZeroFunctor R G X) ∧
    PreservesFiniteColimits (Godement.smoothZeroFunctor R G X)

/-- Every term functor of the smooth Godement complex is additive and exact. -/
def SmoothGodementTermExactStatement (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
    [HasStableNeighbourhoods G X] : Prop :=
  ∀ m : ℕ,
    let T := Langlands.Cohomology.CokernelComplex.term
      (Godement.smoothZeroFunctor R G X) (Godement.smoothCoaugmentation R G X) m
    T.Additive ∧ PreservesFiniteLimits T ∧ PreservesFiniteColimits T

/-- Every term of the smooth Godement complex of a smooth sheaf has no
compactly supported Godement cohomology in positive degrees. -/
def SmoothGodementCompactAcyclicStatement (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MulAction G X] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] : Prop :=
  ∀ (F : SmoothTopologicalSheaf R G X) (m q : ℕ),
    IsZero ((EquivariantGodementCohomology.compactCohomology R G X (q + 1)).obj
      ((Langlands.Sheaf.Equivariant.smoothInclusion R G X).obj
        ((Godement.smoothComplex R G X F).X m)))

/-- Every term of the smooth Godement complex of a smooth sheaf is acyclic for
the derived compact sections of smooth sheaves. -/
def SmoothGodementCompactDerivedAcyclicStatement (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MulAction G X] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] : Prop :=
  ∀ (F : SmoothTopologicalSheaf R G X) (m q : ℕ),
    IsZero ((SmoothSheafCohomology.compactDerived R G X (q + 1)).obj
      ((Godement.smoothComplex R G X F).X m))

/-- The exactness and compact acyclicity statements together. No component is
assumed to define the conjunction. -/
def SmoothGodementStatements (R : Type u) [CommRing R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MulAction G X] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] : Prop :=
  SmoothGodementZeroExactStatement R G X ∧ SmoothGodementTermExactStatement R G X ∧
    SmoothGodementCompactAcyclicStatement R G X ∧
    SmoothGodementCompactDerivedAcyclicStatement R G X

end Langlands.Cohomology.SmoothGodement
