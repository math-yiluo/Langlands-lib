import Langlands.Cohomology.DivisibleSystem.InvariantHomSystem
import Langlands.Cohomology.DivisibleSystem.PowTorsionProjective

/-!
# Surjectivity of the Hom transitions out of invariants

Let `S` be a normal subgroup of a group `G`. For a representation `A` of `G`, the map
`invariantsToCoinvariants A.ρ S` from the `S`-invariants to the `S`-coinvariants of `A` is the
component at `A` of the published natural transformation `invariantsToCoinvariantsNatTrans`. When
it is bijective, the `S`-invariants of `A` behave like its `S`-coinvariants, which are left
adjoint to inflation along `G → G ⧸ S`. This module draws two consequences.

* `epi_quotientToInvariantsFunctor_map`: an epimorphism `A ⟶ B` stays an epimorphism on
  `S`-invariants if `invariantsToCoinvariants` is bijective on `A` and on `B`.
* `powTorsionProjective_quotientToCoinvariants`, `powTorsionProjective_quotientToInvariants`:
  the `S`-coinvariants of a representation `P` with the published hypothesis
  `PowTorsionProjective ℓ m` have it, and so do the `S`-invariants of `P` if
  `invariantsToCoinvariants` is bijective on `P`.

For an `ℓ`-divisible system `T` of representations of `G` on which `invariantsToCoinvariants` is
bijective at every level, the first consequence gives the hypothesis of `mapLeftExact` for the
`S`-invariants functor (`epi_quotientToInvariantsFunctor_map_projection`), so that the
`ℓ`-divisible system `T^S = T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT` of the
published module `InvariantHomSystem` is defined; `invariantsSystem` is this system with the
hypothesis so supplied, and `invariantsComplexSystem` its analogue for `ℓ`-divisible systems of
cochain complexes. If moreover every `T m` satisfies
`PowTorsionProjective ℓ m`, the second consequence and the published module `HomSurjective` show,
for every `ℓ`-divisible system `W` of representations of `G ⧸ S`, that the transitions of the
inverse system `m ↦ Hom((T m)^S, W m)` are surjective
(`invariants_homSystem_map_surjective`), that this system satisfies the Mittag-Leffler condition
(`isMittagLeffler_invariants_homSystem`), and that every morphism `(T n)^S ⟶ W n` is the
level-`n` component of a morphism of inverse systems `T^S ⟶ W`
(`invariants_towerHomEval_surjective`). The same statements hold for the degree `j` terms of an
`ℓ`-divisible system of cochain complexes and its degreewise `S`-invariants
(`epi_quotientToInvariantsFunctor_map_projection_f`,
`degree_invariants_homSystem_map_surjective`, `isMittagLeffler_degree_invariants_homSystem`,
`degree_invariants_towerHomEval_surjective`). For an `ℓ`-divisible system of complexes of smooth
representations, `epi_smoothQuotientInvariants_map_projection_f_of_bijective` derives from the same
bijectivity, on the underlying terms, the hypothesis of the published
`quotientInvariantsComplexes`.

Source: Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39-2 (1999), proof of Proposition 4.10, printed p.312: "But we have seen in §2 that the
maps `C^j_{m+1}(ẽ)^{H_p} → C^j_m(ẽ)^{H_p}` are surjective. Since `C^j_m(ẽ)^{H_p}` and
`Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps
(4.10.3) are surjective for all `m`." In our reading `T` plays the role of the system of degree
`j` terms `C^j_m(ẽ)`, `W` that of the coefficients, the published hypothesis
`PowTorsionProjective` that of freeness, and the bijectivity of `invariantsToCoinvariants` that of
the hypothesis that `p` is prime to `ℓ` (for the compact inductions below, bijectivity holds when
the index, for Harris a power of `p`, is a unit). The surjectivity of the maps on `H_p`-invariants, which
Harris takes from §2, is derived here from the bijectivity hypothesis instead; this route, the
correspondence and the proofs are ours. The bijectivity hypothesis is explicit. At a level `m`
where `T m` is the compact induction of a trivial representation from an open subgroup `H ≤ S`
whose index in `S` is a unit, it is the published
`bijective_invariantsToCoinvariants_compactInduced`. Harris's modules `C^j_m(ẽ)` and
`T_m(j, ẽ)`, his maps (4.10.3), and the freeness of his modules are not formalized here.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite Langlands.Induction

universe w v u uR uG uV

namespace DivisibleSystem

section Objects

variable {k : Type u} [CommRing k] {G : Type v} [Group G] (S : Subgroup G) [S.Normal] {ℓ m : ℕ}

/-- An epimorphism `f : A ⟶ B` of representations of `G` stays an epimorphism on
`S`-invariants when `invariantsToCoinvariants` is bijective on `A` and on `B`: it is then
identified with the map of `S`-coinvariants, which preserve epimorphisms as a left adjoint. -/
lemma epi_quotientToInvariantsFunctor_map {A B : Rep.{w} k G} (f : A ⟶ B) [Epi f]
    (hA : Function.Bijective (invariantsToCoinvariants A.ρ S))
    (hB : Function.Bijective (invariantsToCoinvariants B.ρ S)) :
    Epi ((Rep.quotientToInvariantsFunctor k S).map f) := by
  have := isIso_invariantsToCoinvariantsNatTrans_app A hA
  have := isIso_invariantsToCoinvariantsNatTrans_app B hB
  have := Functor.preservesEpimorphisms_of_adjunction (coinvariantsInflationAdjunction k S)
  have : Epi ((Rep.quotientToCoinvariantsFunctor k S).map f) := Functor.map_epi _ f
  rw [← Category.comp_id ((Rep.quotientToInvariantsFunctor k S).map f),
    ← IsIso.hom_inv_id ((invariantsToCoinvariantsNatTrans k S).app B), ← Category.assoc,
    (invariantsToCoinvariantsNatTrans k S).naturality f]
  infer_instance

/-- The `S`-coinvariants of a representation projective relative to objects killed by `ℓ ^ m`
are projective relative to objects killed by `ℓ ^ m`: coinvariants are left adjoint to
inflation, which is additive and preserves epimorphisms. -/
lemma powTorsionProjective_quotientToCoinvariants {P : Rep.{w} k G}
    (hP : PowTorsionProjective ℓ m P) :
    PowTorsionProjective ℓ m ((Rep.quotientToCoinvariantsFunctor k S).obj P) :=
  powTorsionProjective_obj_of_adjunction (coinvariantsInflationAdjunction k S) hP

/-- The `S`-invariants of a representation `P` projective relative to objects killed by
`ℓ ^ m` are projective relative to objects killed by `ℓ ^ m`, when `invariantsToCoinvariants`
is bijective on `P`: they are then isomorphic to the `S`-coinvariants. -/
lemma powTorsionProjective_quotientToInvariants {P : Rep.{w} k G}
    (hP : PowTorsionProjective ℓ m P)
    (hbij : Function.Bijective (invariantsToCoinvariants P.ρ S)) :
    PowTorsionProjective ℓ m ((Rep.quotientToInvariantsFunctor k S).obj P) :=
  have := isIso_invariantsToCoinvariantsNatTrans_app P hbij
  powTorsionProjective_of_iso (asIso ((invariantsToCoinvariantsNatTrans k S).app P)).symm
    (powTorsionProjective_quotientToCoinvariants S hP)

end Objects

section HomSystem

variable (k : Type u) [CommRing k] {G : Type v} [Group G] (S : Subgroup G) [S.Normal] {ℓ : ℕ}
  (T : DivisibleSystem (Rep.{w} k G) ℓ)
  (hbij : ∀ m : ℕ, Function.Bijective (invariantsToCoinvariants (T.obj m).ρ S))

include hbij in
/-- The projections of `T` stay epimorphisms on `S`-invariants when `invariantsToCoinvariants`
is bijective at every level of `T`. This is the hypothesis of `mapLeftExact` for the
`S`-invariants functor. -/
lemma epi_quotientToInvariantsFunctor_map_projection {m' m : ℕ} (h : m' ≤ m) :
    Epi ((Rep.quotientToInvariantsFunctor k S).map (T.projection h)) :=
  have := T.epi_projection h
  epi_quotientToInvariantsFunctor_map S (T.projection h) (hbij m) (hbij m')

/-- The `ℓ`-divisible system `m ↦ (T m)^S` of representations of `G ⧸ S` formed by the
`S`-invariants of `T`, when `invariantsToCoinvariants` is bijective at every level of `T`. It is
`T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT` for the hypothesis `hT` supplied by
`epi_quotientToInvariantsFunctor_map_projection`. -/
def invariantsSystem : DivisibleSystem (Rep.{w} k (G ⧸ S)) ℓ :=
  T.mapLeftExact (Rep.quotientToInvariantsFunctor k S)
    (epi_quotientToInvariantsFunctor_map_projection k S T hbij)

/-- `invariantsSystem` agrees with `mapLeftExact` for any proof of its hypothesis, so the
statements below about `T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT` apply to it. -/
lemma invariantsSystem_eq_mapLeftExact
    (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi ((Rep.quotientToInvariantsFunctor k S).map (T.projection h))) :
    invariantsSystem k S T hbij = T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT :=
  rfl

lemma invariantsSystem_obj (m : ℕ) :
    (invariantsSystem k S T hbij).obj m = (Rep.quotientToInvariantsFunctor k S).obj (T.obj m) :=
  rfl

variable (hT : ∀ {m' m : ℕ} (h : m' ≤ m),
    Epi ((Rep.quotientToInvariantsFunctor k S).map (T.projection h)))
  (hP : ∀ m, PowTorsionProjective ℓ m (T.obj m))
  (W : DivisibleSystem (Rep.{w} k (G ⧸ S)) ℓ)

include hbij hP in
/-- Every level `(T m)^S` of the `S`-invariants of `T` is projective relative to objects
killed by `ℓ ^ m`, when `T m` is and `invariantsToCoinvariants` is bijective on `T m`. -/
lemma powTorsionProjective_mapLeftExact_quotientToInvariants (m : ℕ) :
    PowTorsionProjective ℓ m ((T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT).obj m) :=
  powTorsionProjective_quotientToInvariants S (hP m) (hbij m)

include hbij hP in
/-- Harris 1999, p.312, surjectivity of the maps (4.10.3) for invariants: the transitions of
the inverse system `m ↦ Hom((T m)^S, W m)` are surjective. -/
lemma invariants_homSystem_map_surjective {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective
      ((homSystem k (T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT) W).map φ) :=
  homSystem_map_surjective k _ W
    (powTorsionProjective_mapLeftExact_quotientToInvariants k S T hbij hT hP) φ

include hbij hP in
/-- The inverse system `m ↦ Hom((T m)^S, W m)` satisfies the Mittag-Leffler condition. -/
lemma isMittagLeffler_invariants_homSystem :
    (homSystem k (T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT) W ⋙
      CategoryTheory.forget _).IsMittagLeffler :=
  isMittagLeffler_homSystem k _ W
    (powTorsionProjective_mapLeftExact_quotientToInvariants k S T hbij hT hP)

include hbij hP in
/-- Every morphism `(T n)^S ⟶ W n` is the level-`n` component of a morphism of inverse systems
`T^S ⟶ W`. -/
lemma invariants_towerHomEval_surjective (n : ℕ) :
    Function.Surjective
      (towerHomEval k (T.mapLeftExact (Rep.quotientToInvariantsFunctor k S) hT) W n) :=
  towerHomEval_surjective k _ W
    (powTorsionProjective_mapLeftExact_quotientToInvariants k S T hbij hT hP) n

end HomSystem

section Complexes

variable (k : Type u) [CommRing k] {G : Type v} [Group G] (S : Subgroup G) [S.Normal] {ℓ : ℕ}
  (K : DivisibleSystem (CochainComplex (Rep.{w} k G) ℕ) ℓ)
  (hbij : ∀ m q : ℕ, Function.Bijective (invariantsToCoinvariants ((K.obj m).X q).ρ S))

include hbij in
/-- The degreewise projections of `K` stay epimorphisms on `S`-invariants when
`invariantsToCoinvariants` is bijective on every term of `K`. This is the hypothesis of
`mapComplexes` for the `S`-invariants functor. -/
lemma epi_quotientToInvariantsFunctor_map_projection_f {m' m : ℕ} (h : m' ≤ m) (q : ℕ) :
    Epi ((Rep.quotientToInvariantsFunctor k S).map ((K.projection h).f q)) :=
  epi_quotientToInvariantsFunctor_map_projection k S (K.degree q) (fun m => hbij m q) h

/-- The `ℓ`-divisible system `m ↦ K_m^S` of cochain complexes of representations of `G ⧸ S`
formed by the degreewise `S`-invariants of `K`, when `invariantsToCoinvariants` is bijective on
every term of `K`. It is `K.mapComplexes (Rep.quotientToInvariantsFunctor k S) hK` for the
hypothesis `hK` supplied by `epi_quotientToInvariantsFunctor_map_projection_f`. -/
def invariantsComplexSystem : DivisibleSystem (CochainComplex (Rep.{w} k (G ⧸ S)) ℕ) ℓ :=
  K.mapComplexes (Rep.quotientToInvariantsFunctor k S)
    (epi_quotientToInvariantsFunctor_map_projection_f k S K hbij)

/-- `invariantsComplexSystem` agrees with `mapComplexes` for any proof of its hypothesis. -/
lemma invariantsComplexSystem_eq_mapComplexes
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((Rep.quotientToInvariantsFunctor k S).map ((K.projection h).f q))) :
    invariantsComplexSystem k S K hbij = K.mapComplexes (Rep.quotientToInvariantsFunctor k S) hK :=
  rfl

lemma invariantsComplexSystem_obj_X (m q : ℕ) :
    ((invariantsComplexSystem k S K hbij).obj m).X q =
      (Rep.quotientToInvariantsFunctor k S).obj ((K.obj m).X q) :=
  rfl

variable (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
    Epi ((Rep.quotientToInvariantsFunctor k S).map ((K.projection h).f q)))
  (j : ℕ) (hP : ∀ m, PowTorsionProjective ℓ m ((K.obj m).X j))
  (W : DivisibleSystem (Rep.{w} k (G ⧸ S)) ℓ)

include hbij hP in
/-- The degree-`j` transitions of the inverse system `m ↦ Hom((K_m^S)^j, W m)` are surjective
when every `K_m^j` is projective relative to objects killed by `ℓ ^ m`. -/
lemma degree_invariants_homSystem_map_surjective {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective
      ((homSystem k ((K.mapComplexes (Rep.quotientToInvariantsFunctor k S) hK).degree j) W).map
        φ) :=
  invariants_homSystem_map_surjective k S (K.degree j) (fun m => hbij m j)
    (fun h => hK h j) hP W φ

include hbij hP in
/-- The degree-`j` inverse system `m ↦ Hom((K_m^S)^j, W m)` satisfies the Mittag-Leffler
condition when every `K_m^j` is projective relative to objects killed by `ℓ ^ m`. -/
lemma isMittagLeffler_degree_invariants_homSystem :
    (homSystem k ((K.mapComplexes (Rep.quotientToInvariantsFunctor k S) hK).degree j) W ⋙
      CategoryTheory.forget _).IsMittagLeffler :=
  isMittagLeffler_invariants_homSystem k S (K.degree j) (fun m => hbij m j)
    (fun h => hK h j) hP W

include hbij hP in
/-- Every morphism `(K_n^S)^j ⟶ W n` is the level-`n` component of a morphism of inverse
systems `(K^S)^j ⟶ W`. -/
lemma degree_invariants_towerHomEval_surjective (n : ℕ) :
    Function.Surjective
      (towerHomEval k ((K.mapComplexes (Rep.quotientToInvariantsFunctor k S) hK).degree j) W
        n) :=
  invariants_towerHomEval_surjective k S (K.degree j) (fun m => hbij m j)
    (fun h => hK h j) hP W n

end Complexes

section Smooth

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {ℓ : ℕ}
  (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, uV} R G) ℕ) ℓ)
  (H : Subgroup G) [H.Normal]
  (hbij : ∀ m q : ℕ,
    Function.Bijective (invariantsToCoinvariants (SmoothRep.toRep.obj ((K.obj m).X q)).ρ H))

include hbij in
/-- For an `ℓ`-divisible system of complexes of smooth representations, the degreewise
projections stay epimorphisms on `H`-invariants when `invariantsToCoinvariants` is bijective on
every underlying term. This is the hypothesis of the published `quotientInvariantsComplexes`. -/
lemma epi_smoothQuotientInvariants_map_projection_f_of_bijective {m' m : ℕ} (h : m' ≤ m) (q : ℕ) :
    Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)) :=
  have := K.epi_toRep_map_projection_f h q
  epi_quotientToInvariantsFunctor_map H (SmoothRep.toRep.map ((K.projection h).f q))
    (hbij m q) (hbij m' q)

end Smooth

end DivisibleSystem

end Langlands.Cohomology
