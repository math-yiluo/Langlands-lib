import Langlands.Geometry.Building.SpecialCompactLevi
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness

/-!
# Properties of a special maximal compact subgroup

Proposition-valued predicates on a subgroup `K` of the actual rational points `G(k)`, for the
properties of a special maximal compact subgroup in KP Theorem 4.2.15(1) and Renard,
Théorème V.5.1(2), (3), (5):

* `IsBoundedOpenMaximal F K`: `K` is algebraically bounded (KP Definition 2.2.1), open, and
  maximal among bounded subgroups;
* `IsCompactOpenMaximal F K`: `K` is compact, open, and maximal among compact subgroups;
* `HasWeylRepresentatives i K`: every element of the relative Weyl group `N(k)/Z(k)` has a
  representative in `N(k) ∩ K`;
* `HasParabolicFactorization i ν K`: `K ∩ P_J = (K ∩ M_J)(K ∩ U_J)` in `G(k)` for every set `J`
  of simple relative roots;
* `SpecialCompactProperties F i ν K`: the conjunction of the four;
* `IsLeviRestriction j y yM`: the point `yM` of an apartment of `M` is the restriction of the
  valuation `y` to the relative roots of `M` (KP Lemma 6.7.1);
* `SpecialLeviRestriction F ν D x J DM xM`: the point `xM` of Levi data `DM` for the actual
  standard Levi `M_J` is a special vertex restricted from `x` whose compact stabilizer has the
  same properties and is the preimage of `K_x` in `M_J(F)` (Renard, Théorème V.5.1(5); KP §6.7);
* `SpecialLeviInheritance F hi ν D x`: for every `J`, such Levi data and such a point exist.

The topology on `G(k)` is the named `rationalPointTopology`; no topology instance is declared.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Pointwise
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

section General

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Every element of the relative Weyl group `W = N(k)/Z(k)` has a representative in `K`, that
is, `N(k) ∩ K → W` is surjective (Renard, Théorème V.5.1(2)). -/
def HasWeylRepresentatives (i : S.toGrp ⟶ G) (K : Subgroup (rationalPoints G)) : Prop :=
  ∀ w : relativeWeylGroup i, ∃ n : normalizerPoints i,
    (n : rationalPoints G) ∈ K ∧ (QuotientGroup.mk n : relativeWeylGroup i) = w

/-- For every set `J` of simple relative roots (for the positive system of `ν`), the literal
identity `K ∩ P_J = (K ∩ M_J)(K ∩ U_J)` of subsets of `G(k)`, for the actual standard parabolic
`P_J`, standard Levi `M_J` and standard unipotent radical `U_J` (Renard, Théorème V.5.1(3)). -/
def HasParabolicFactorization [IsAffineHom G.X.hom] (i : S.toGrp ⟶ G)
    (ν : cocharacterLattice S) (K : Subgroup (rationalPoints G)) : Prop :=
  ∀ J ⊆ simpleRelativeRoots i ν,
    ((K ⊓ standardParabolicPoints i ν J : Subgroup (rationalPoints G)) :
        Set (rationalPoints G)) =
      ((K ⊓ standardLeviPoints i ν J : Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
        ((K ⊓ standardUnipotentPoints i ν J : Subgroup (rationalPoints G)) :
          Set (rationalPoints G))

end General

section Topological

variable (F : Type u) [Field F] [TopologicalSpace F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]

/-- KP Theorem 4.2.15(1), source form: `K` is algebraically bounded in the sense of KP
Definition 2.2.1, open for the rational-point topology, and maximal among algebraically
bounded subgroups of `G(F)`. -/
def IsBoundedOpenMaximal [ValuativeRel F] (K : Subgroup (rationalPoints G)) : Prop :=
  haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  IsAlgebraicallyBounded F G.X (K : Set (rationalPoints G)) ∧
    IsOpen (K : Set (rationalPoints G)) ∧
    Maximal (fun L : Subgroup (rationalPoints G) =>
      IsAlgebraicallyBounded F G.X (L : Set (rationalPoints G))) K

/-- Local-field form (Renard, Théorème V.5.1): `K` is compact and open for the rational-point
topology, and maximal among compact subgroups of `G(F)`. -/
def IsCompactOpenMaximal (K : Subgroup (rationalPoints G)) : Prop :=
  haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  IsCompact (K : Set (rationalPoints G)) ∧ IsOpen (K : Set (rationalPoints G)) ∧
    Maximal (fun L : Subgroup (rationalPoints G) => IsCompact (L : Set (rationalPoints G))) K

/-- The properties of a special maximal compact subgroup `K` adapted to `(S, ν)`: KP Theorem
4.2.15(1) in both its bounded and its compact form, and Renard, Théorème V.5.1(2) and (3). -/
def SpecialCompactProperties [ValuativeRel F] {S : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (K : Subgroup (rationalPoints G)) : Prop :=
  IsBoundedOpenMaximal F K ∧ IsCompactOpenMaximal F K ∧ HasWeylRepresentatives i K ∧
    HasParabolicFactorization i ν K

end Topological

section Levi

open Langlands.Geometry.Building

/-- `yM` is the restriction along `j : M → G` of the valuation `y` (KP §6.7, Lemma 6.7.1:
`φ_M = (φ_a)_{a ∈ Φ(M, S)}`): `yM_a(m) = y_a(j m)` for every relative root `a` of `(M, S)` and
every `m ∈ M(k)`. -/
def IsLeviRestriction {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G M : GroupScheme (Spec (CommRingCat.of k))} (j : M ⟶ G) {i : S.toGrp ⟶ G}
    {iM : S.toGrp ⟶ M} [Mono i.hom.hom.left] [IsAffineHom G.X.hom] [Mono iM.hom.hom.left]
    [IsAffineHom M.X.hom] {ω : kˣ → ℝ} {D : KPApartmentData i ω} {DM : KPApartmentData iM ω}
    (y : D.Apartment) (yM : DM.Apartment) : Prop :=
  ∀ a ∈ relativeRoots iM, ∀ m : rationalPoints M, yM.val a m = y.val a (rationalPoints.map j m)

/-- The per-`J` relation between the ambient data `(D, x)` and Levi data `(DM, xM)` (Renard,
Théorème V.5.1(5); KP §6.7). Let `M_J = Standard.leviScheme i ν J` be the actual closed standard
Levi, `Standard.leviHom i ν J : M_J → G` its inclusion and `Standard.leviTorusHom i ν J : S → M_J`
the same torus. Then `xM` is a special vertex of the apartment of `DM` and the restriction of
`x`, and `K^M_{xM} = M_J(F)^1 ∩ M_J(F)_{xM}` has the properties `SpecialCompactProperties` for
`(M_J, S, ν)` and equals the preimage `D.specialCompactLeviSubgroup ν J x` of `K_x` in `M_J(F)`,
whose image in `G(F)` is `K_x ∩ M_J(F)`. -/
def SpecialLeviRestriction (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] {i : S.toGrp ⟶ G}
    [Mono i.hom.hom.left] (ν : cocharacterLattice S) (D : KPApartmentData i (localFieldOrder F))
    (x : D.Apartment) (J : Set (characterLattice S))
    [IsAffineHom (Standard.leviScheme i ν J).X.hom]
    [Mono (Standard.leviTorusHom i ν J).hom.hom.left]
    (DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F))
    (xM : DM.Apartment) : Prop :=
  DM.IsSpecialApartmentVertex xM ∧
    IsLeviRestriction (Standard.leviHom i ν J) x xM ∧
    SpecialCompactProperties F (Standard.leviTorusHom i ν J) ν (DM.specialCompactSubgroup xM) ∧
    DM.specialCompactSubgroup xM = D.specialCompactLeviSubgroup ν J x

/-- Inheritance by the standard Levi subgroups (Renard, Théorème V.5.1(5); KP §6.7): for every
set `J` of simple relative roots there are apartment data `DM` for `(M_J, S)` and a point `xM`
with `SpecialLeviRestriction F ν D x J DM xM`. The instances on `M_J` and on the torus
`S → M_J` are the published ones. -/
def SpecialLeviInheritance (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] {i : S.toGrp ⟶ G}
    [Mono i.hom.hom.left] (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
    (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment) : Prop :=
  ∀ J ⊆ simpleRelativeRoots i ν,
    haveI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
      (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
    haveI : Mono (Standard.leviTorusHom i ν J).hom.hom.left :=
      (Standard.isMaximalSplitTorus_leviTorusHom i ν J hi).isSplitSubtorus.mono
    ∃ (DM : KPApartmentData (Standard.leviTorusHom i ν J) (localFieldOrder F))
      (xM : DM.Apartment), SpecialLeviRestriction F ν D x J DM xM

end Levi

end Langlands.BruhatTits.SpecialCompact
