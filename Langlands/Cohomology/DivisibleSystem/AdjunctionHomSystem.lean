import Langlands.Cohomology.DivisibleSystem.HomSystem
import Langlands.Cohomology.SupercuspidalExt.Reciprocity
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Adjunction isomorphisms of Hom complexes and of Hom-complex systems

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, proof of
Proposition 4.10, p.311: the complexes used for the spectral sequences (4.9) have terms
`⊕_{i+j=k} Hom_{𝒪/ℓ^m𝒪[GJ]}(⊕_{(e,δ) ∈ O_{-i}} c-Ind_{S(ẽ)}^{GJ} C^j_m(ẽ),
Hom(𝒪_m[K_p/H_p]^M, 𝓛_m))`, "which can be rewritten" as (4.10.2)
`⊕_{i+j=k} ⊕_{(e,δ) ∈ O_{-i}} Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ), Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`.
The main step of this rewriting is Frobenius reciprocity for compact induction from the
open subgroup `S(ẽ)`; this module treats that step for Hom complexes. The splitting of the
sum over `(e, δ)` and the passage from `K_p` to `C_p` in the coefficients are not treated.

For an adjunction `F ⊣ G` between `R`-linear categories with `F` and `G` additive and `G`
`R`-linear, this module constructs:

* `LinearHomComplex.cochainLinearEquiv`: the `R`-linear equivalence of graded morphisms
  `Cochain (F K) L n ≃ Cochain K (G L) n`, applying the hom-equivalence of the adjunction
  to every component;
* `LinearHomComplex.adjunctionIso`: the resulting isomorphism of Hom complexes
  `Hom^•(F K, L) ≅ Hom^•(K, G L)`, natural in `K` and `L`
  (`LinearHomComplex.map_comp_adjunctionIso_hom`);
* `DivisibleSystem.homComplexSystemAdjunctionIso`: for exact `F` and `G`, an `ℓ`-divisible
  system of cochain complexes `T` and an `ℓ`-divisible system of cochain complexes `W`, the
  isomorphism of inverse systems of Hom complexes `m ↦ Hom^•(F (T m), W m)` and
  `m ↦ Hom^•(T m, G (W m))`, and the isomorphism of their limits.

For an open subgroup `H` of a topological group `G`, compact induction (additive by
`compactInduction_additive`, exact by `compactInduction_preservesHomology`) and restriction
of smooth representations are exact and adjoint, and the last construction gives
`smoothHomComplexSystemReciprocityIso`: the inverse system of Hom complexes from the compact
induction of an `ℓ`-divisible system `T` of complexes of smooth representations of `H` into
an `ℓ`-divisible system `W` of complexes of smooth representations of `G` is isomorphic to
the inverse system of Hom complexes from `T` into the restriction of `W`. This is the shape
of Harris's rewriting with `H = S(ẽ)`; the identification of Harris's complexes with Hom
complexes of this kind is not formalized here.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

universe w v u u'

namespace LinearHomComplex

section Adjunction

variable (R : Type w) [Ring R]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type u'} [Category.{v} D] [Preadditive D] [Linear R D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.Additive] [G.Linear R]

/-- The hom-equivalence `(F X ⟶ Y) ≃ (X ⟶ G Y)` of an adjunction `F ⊣ G` with `G`
`R`-linear, as an `R`-linear equivalence. -/
def adjunctionHomLinearEquiv (X : C) (Y : D) : (F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) where
  __ := adj.homEquiv X Y
  map_add' f g := by
    change adj.homEquiv X Y (f + g) = adj.homEquiv X Y f + adj.homEquiv X Y g
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      Functor.map_add, Preadditive.comp_add]
  map_smul' r f := by
    change adj.homEquiv X Y (r • f) = r • adj.homEquiv X Y f
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_smul, Linear.comp_smul]

lemma adjunctionHomLinearEquiv_apply (X : C) (Y : D) (f : F.obj X ⟶ Y) :
    adjunctionHomLinearEquiv R adj X Y f = adj.homEquiv X Y f :=
  rfl

lemma adjunctionHomLinearEquiv_symm_apply (X : C) (Y : D) (g : X ⟶ G.obj Y) :
    (adjunctionHomLinearEquiv R adj X Y).symm g = (adj.homEquiv X Y).symm g :=
  rfl

variable [F.Additive] (K K' : CochainComplex C ℤ) (L L' : CochainComplex D ℤ)

/-- Transpose of graded morphisms across `F ⊣ G`: the component `F (K p) ⟶ L q` of a graded
morphism `F K ⟶ L` of degree `n` is sent to the corresponding component `K p ⟶ G (L q)` by
the hom-equivalence of the adjunction. -/
def cochainLinearEquiv (n : ℤ) :
    Cochain ((F.mapHomologicalComplex _).obj K) L n ≃ₗ[R]
      Cochain K ((G.mapHomologicalComplex _).obj L) n where
  toFun z := Cochain.mk fun p q hpq => adj.homEquiv (K.X p) (L.X q) (z.v p q hpq)
  invFun z := Cochain.mk fun p q hpq => (adj.homEquiv (K.X p) (L.X q)).symm (z.v p q hpq)
  map_add' z z' := by
    ext p q hpq
    rw [Cochain.mk_v, Cochain.add_v, Cochain.add_v, Cochain.mk_v, Cochain.mk_v]
    exact (adjunctionHomLinearEquiv R adj (K.X p) (L.X q)).map_add _ _
  map_smul' r z := by
    ext p q hpq
    rw [Cochain.mk_v, Cochain.smul_v, Cochain.smul_v, Cochain.mk_v]
    exact (adjunctionHomLinearEquiv R adj (K.X p) (L.X q)).map_smul _ _
  left_inv z := by
    ext p q hpq
    rw [Cochain.mk_v, Cochain.mk_v]
    exact (adj.homEquiv (K.X p) (L.X q)).symm_apply_apply _
  right_inv z := by
    ext p q hpq
    rw [Cochain.mk_v, Cochain.mk_v]
    exact (adj.homEquiv (K.X p) (L.X q)).apply_symm_apply _

variable {K L}

@[simp]
lemma cochainLinearEquiv_v {n : ℤ} (z : Cochain ((F.mapHomologicalComplex _).obj K) L n)
    (p q : ℤ) (hpq : p + n = q) :
    (cochainLinearEquiv R adj K L n z).v p q hpq = adj.homEquiv (K.X p) (L.X q) (z.v p q hpq) :=
  rfl

@[simp]
lemma cochainLinearEquiv_symm_v {n : ℤ} (z : Cochain K ((G.mapHomologicalComplex _).obj L) n)
    (p q : ℤ) (hpq : p + n = q) :
    ((cochainLinearEquiv R adj K L n).symm z).v p q hpq =
      (adj.homEquiv (K.X p) (L.X q)).symm (z.v p q hpq) :=
  rfl

variable (K) in
/-- The unit of `F ⊣ G` on a cochain complex, as a chain map `K ⟶ G (F K)`. -/
def unitHom :
    K ⟶ (G.mapHomologicalComplex _).obj ((F.mapHomologicalComplex _).obj K) where
  f p := adj.unit.app (K.X p)
  comm' p q _ := (adj.unit.naturality (K.d p q)).symm

/-- The transpose of a graded morphism `z : F K ⟶ L` is the composite of the unit
`K ⟶ G (F K)` with `G z`. -/
lemma cochainLinearEquiv_eq_comp {n : ℤ}
    (z : Cochain ((F.mapHomologicalComplex _).obj K) L n) :
    cochainLinearEquiv R adj K L n z =
      (Cochain.ofHom (unitHom adj K)).comp (z.map G) (zero_add n) := by
  ext p q hpq
  rw [cochainLinearEquiv_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.map_v,
    Adjunction.homEquiv_unit]
  rfl

/-- The transpose of graded morphisms commutes with the differentials of the Hom
complexes. -/
lemma δ_cochainLinearEquiv (n m : ℤ) (z : Cochain ((F.mapHomologicalComplex _).obj K) L n) :
    δ n m (cochainLinearEquiv R adj K L n z) = cochainLinearEquiv R adj K L m (δ n m z) := by
  rw [cochainLinearEquiv_eq_comp, cochainLinearEquiv_eq_comp, δ_ofHom_comp, δ_map]

/-- The transpose is natural in the source complex. -/
lemma cochainLinearEquiv_ofHom_comp (f : K' ⟶ K) {n : ℤ}
    (z : Cochain ((F.mapHomologicalComplex _).obj K) L n) :
    cochainLinearEquiv R adj K' L n
        ((Cochain.ofHom ((F.mapHomologicalComplex _).map f)).comp z (zero_add n)) =
      (Cochain.ofHom f).comp (cochainLinearEquiv R adj K L n z) (zero_add n) := by
  ext p q hpq
  rw [cochainLinearEquiv_v, Cochain.zero_cochain_comp_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v, cochainLinearEquiv_v]
  exact adj.homEquiv_naturality_left (f.f p) (z.v p q hpq)

/-- The transpose is natural in the target complex. -/
lemma cochainLinearEquiv_comp_ofHom (g : L ⟶ L') {n : ℤ}
    (z : Cochain ((F.mapHomologicalComplex _).obj K) L n) :
    cochainLinearEquiv R adj K L' n (z.comp (Cochain.ofHom g) (add_zero n)) =
      (cochainLinearEquiv R adj K L n z).comp
        (Cochain.ofHom ((G.mapHomologicalComplex _).map g)) (add_zero n) := by
  ext p q hpq
  rw [cochainLinearEquiv_v, Cochain.comp_zero_cochain_v, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, Cochain.ofHom_v, cochainLinearEquiv_v]
  exact adj.homEquiv_naturality_right (z.v p q hpq) (g.f q)

variable (K L) in
/-- Harris 1999, p.311, the rewriting to (4.10.2) for an adjunction `F ⊣ G`: the Hom complex
`Hom^•(F K, L)` is isomorphic to the Hom complex `Hom^•(K, G L)`, by the transpose of
graded morphisms in every degree. -/
def adjunctionIso :
    complex R ((F.mapHomologicalComplex _).obj K) L ≅
      complex R K ((G.mapHomologicalComplex _).obj L) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (cochainLinearEquiv R adj K L n).toModuleIso)
    (fun n m _ => by
      ext z
      exact δ_cochainLinearEquiv R adj n m z)

lemma adjunctionIso_hom_f_apply {n : ℤ}
    (z : Cochain ((F.mapHomologicalComplex _).obj K) L n) :
    (adjunctionIso R adj K L).hom.f n z = cochainLinearEquiv R adj K L n z :=
  rfl

/-- The isomorphism `adjunctionIso` is natural in both complexes. -/
lemma map_comp_adjunctionIso_hom (f : K' ⟶ K) (g : L ⟶ L') :
    map R ((F.mapHomologicalComplex _).map f) g ≫ (adjunctionIso R adj K' L').hom =
      (adjunctionIso R adj K L).hom ≫ map R f ((G.mapHomologicalComplex _).map g) := by
  ext n z
  change cochainLinearEquiv R adj K' L' n
      (((Cochain.ofHom ((F.mapHomologicalComplex _).map f)).comp z (zero_add n)).comp
        (Cochain.ofHom g) (add_zero n)) =
    ((Cochain.ofHom f).comp (cochainLinearEquiv R adj K L n z) (zero_add n)).comp
      (Cochain.ofHom ((G.mapHomologicalComplex _).map g)) (add_zero n)
  rw [cochainLinearEquiv_comp_ofHom, cochainLinearEquiv_ofHom_comp]

end Adjunction

end LinearHomComplex

namespace DivisibleSystem

section Adjunction

variable (R : Type w) [Ring R]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  {D : Type u'} [Category.{v} D] [Abelian D] [Linear R D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive] [G.Linear R]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {ℓ : ℕ} (T : DivisibleSystem (CochainComplex C ℤ) ℓ) (W : DivisibleSystem (CochainComplex D ℤ) ℓ)

/-- The transpose of graded morphisms commutes with the transitions of the Hom-complex
systems: transposing and then passing from level `m` to level `m'` agrees with passing
from level `m` to level `m'` and then transposing. -/
lemma cochainLinearEquiv_cochainTransition {m' m : ℕ} (h : m' ≤ m) {n : ℤ}
    (z : Cochain ((T.map (F.mapHomologicalComplex _)).obj m) (W.obj m) n) :
    LinearHomComplex.cochainLinearEquiv R adj (T.obj m') (W.obj m') n
        (cochainTransition (T.map (F.mapHomologicalComplex _)) W h z) =
      cochainTransition T (W.map (G.mapHomologicalComplex _)) h
        (LinearHomComplex.cochainLinearEquiv R adj (T.obj m) (W.obj m) n z) := by
  symm
  refine (cochainTransition_eq_iff T (W.map (G.mapHomologicalComplex _)) h _ _).2 ?_
  refine (LinearHomComplex.cochainLinearEquiv_ofHom_comp R adj _ (T.projection h) _).symm.trans
    ?_
  refine (congrArg (LinearHomComplex.cochainLinearEquiv R adj (T.obj m) (W.obj m') n)
    (ofHom_comp_cochainTransition (T.map (F.mapHomologicalComplex _)) W h z)).trans ?_
  exact LinearHomComplex.cochainLinearEquiv_comp_ofHom R adj _ (W.projection h) z

/-- Harris 1999, p.311, the rewriting to (4.10.2) for an adjunction `F ⊣ G` of exact
functors: the inverse system of Hom complexes `m ↦ Hom^•(F (T m), W m)` is isomorphic to the
inverse system `m ↦ Hom^•(T m, G (W m))`, levelwise by `LinearHomComplex.adjunctionIso`. -/
def homComplexSystemAdjunctionIso :
    homComplexSystem R (T.map (F.mapHomologicalComplex _)) W ≅
      homComplexSystem R T (W.map (G.mapHomologicalComplex _)) :=
  NatIso.ofComponents
    (fun m => LinearHomComplex.adjunctionIso R adj (T.obj m.unop) (W.obj m.unop))
    (fun {m m'} φ => by
      ext n z
      exact cochainLinearEquiv_cochainTransition R adj T W (leOfHom φ.unop) z)

lemma homComplexSystemAdjunctionIso_hom_app (m : ℕᵒᵖ) :
    (homComplexSystemAdjunctionIso R adj T W).hom.app m =
      (LinearHomComplex.adjunctionIso R adj (T.obj m.unop) (W.obj m.unop)).hom :=
  rfl

/-- The isomorphism of the inverse limits of the Hom-complex systems induced by
`homComplexSystemAdjunctionIso`. -/
def homComplexLimitAdjunctionIso :
    homComplexLimit R (T.map (F.mapHomologicalComplex _)) W ≅
      homComplexLimit R T (W.map (G.mapHomologicalComplex _)) :=
  HasLimit.isoOfNatIso (homComplexSystemAdjunctionIso R adj T W)

@[reassoc (attr := simp)]
lemma homComplexLimitAdjunctionIso_hom_π (m : ℕᵒᵖ) :
    (homComplexLimitAdjunctionIso R adj T W).hom ≫
        limit.π (homComplexSystem R T (W.map (G.mapHomologicalComplex _))) m =
      limit.π (homComplexSystem R (T.map (F.mapHomologicalComplex _)) W) m ≫
        (LinearHomComplex.adjunctionIso R adj (T.obj m.unop) (W.obj m.unop)).hom :=
  HasLimit.isoOfNatIso_hom_π _ m

end Adjunction

end DivisibleSystem

section Smooth

open SupercuspidalExt

variable (R : Type u) [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {H : Subgroup G} (hH : IsOpen (H : Set G)) {ℓ : ℕ}

/-- Compact induction is additive: it acts on morphisms by composition on values. -/
instance compactInduction_additive : (compactInduction R G H).Additive where
  map_add := by
    intro A B f g
    ext F
    rfl

include hH in
/-- Compact induction from an open subgroup is exact: it preserves monomorphisms, and it
preserves cokernels as a left adjoint. -/
theorem compactInduction_preservesHomology : (compactInduction R G H).PreservesHomology := by
  have := (compactInductionAdjunction R G H hH).leftAdjoint_preservesColimits
  have : (compactInduction R G H).PreservesMonomorphisms :=
    Induction.smoothCompactInduction_preservesMonomorphisms.{u, u, u} R H
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- Compact induction `c-Ind_H^G` applied to every level of an `ℓ`-divisible system of
cochain complexes of smooth representations of an open subgroup `H`. -/
def compactInductionSystem (T : SmoothRepComplexDivisibleSystem.{u, u, u} R H ℓ) :
    SmoothRepComplexDivisibleSystem.{u, u, u} R G ℓ :=
  haveI := compactInduction_preservesHomology R hH
  haveI := Functor.preservesFiniteLimits_of_preservesHomology (compactInduction R G H)
  haveI := Functor.preservesFiniteColimits_of_preservesHomology (compactInduction R G H)
  T.map ((compactInduction R G H).mapHomologicalComplex _)

/-- Restriction to an open subgroup `H` applied to every level of an `ℓ`-divisible system of
cochain complexes of smooth representations of `G`. -/
def restrictionSystem (W : SmoothRepComplexDivisibleSystem.{u, u, u} R G ℓ) :
    SmoothRepComplexDivisibleSystem.{u, u, u} R H ℓ :=
  haveI := restriction_preservesHomology R G hH
  haveI := Functor.preservesFiniteLimits_of_preservesHomology (restriction R G H)
  haveI := Functor.preservesFiniteColimits_of_preservesHomology (restriction R G H)
  W.map ((restriction R G H).mapHomologicalComplex _)

/-- Harris 1999, p.311, the rewriting to (4.10.2), for `ℓ`-divisible systems of cochain
complexes of smooth representations: for an open subgroup `H` of `G`, the inverse system of
Hom complexes `m ↦ Hom^•_G(c-Ind_H^G T m, W m)` is isomorphic to the inverse system
`m ↦ Hom^•_H(T m, W m|_H)`, by Frobenius reciprocity in every component. -/
def smoothHomComplexSystemReciprocityIso (T : SmoothRepComplexDivisibleSystem.{u, u, u} R H ℓ)
    (W : SmoothRepComplexDivisibleSystem.{u, u, u} R G ℓ) :
    smoothHomComplexSystem R G (compactInductionSystem R hH T) W ≅
      smoothHomComplexSystem R H T (restrictionSystem R hH W) :=
  haveI := compactInduction_preservesHomology R hH
  haveI := Functor.preservesFiniteLimits_of_preservesHomology (compactInduction R G H)
  haveI := Functor.preservesFiniteColimits_of_preservesHomology (compactInduction R G H)
  haveI := restriction_preservesHomology R G hH
  haveI := Functor.preservesFiniteLimits_of_preservesHomology (restriction R G H)
  haveI := Functor.preservesFiniteColimits_of_preservesHomology (restriction R G H)
  DivisibleSystem.homComplexSystemAdjunctionIso R (compactInductionAdjunction R G H hH) T W

/-- The isomorphism of the inverse limits of the Hom-complex systems induced by
`smoothHomComplexSystemReciprocityIso`. -/
def smoothHomComplexLimitReciprocityIso (T : SmoothRepComplexDivisibleSystem.{u, u, u} R H ℓ)
    (W : SmoothRepComplexDivisibleSystem.{u, u, u} R G ℓ) :
    DivisibleSystem.homComplexLimit R (compactInductionSystem R hH T) W ≅
      DivisibleSystem.homComplexLimit R T (restrictionSystem R hH W) :=
  HasLimit.isoOfNatIso (smoothHomComplexSystemReciprocityIso R hH T W)

end Smooth

end Langlands.Cohomology
