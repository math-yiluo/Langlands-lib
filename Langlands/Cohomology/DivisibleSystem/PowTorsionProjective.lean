import Langlands.Cohomology.DivisibleSystem.BiproductHomSystem
import Langlands.Cohomology.DivisibleSystem.HomSurjective

/-!
# Relative projectivity of direct sums and compact inductions

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, proof of
Proposition 4.10, p.312: "Since `C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free
`𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3) are surjective for all `m`."
The published module `HomSurjective` abstracts the freeness used there as the hypothesis
`PowTorsionProjective ℓ m P` (every morphism from `P` lifts along epimorphisms whose source is
killed by `ℓ ^ m`) and proves the surjectivity and Mittag-Leffler statements for the inverse
systems of Hom complexes `homComplexSystem R T W` when every term `(T m) ^ p` satisfies it.

This module proves that the hypothesis is preserved by finite direct sums and by compact
induction from open subgroups, the constructions of Harris's (4.4.4) (p.310), so that it can be
checked on the inducing modules:

* `powTorsionProjective_of_iso`, `powTorsionProjective_of_le`: invariance under isomorphism,
  and passage from `ℓ ^ m` to `ℓ ^ m'` for `m' ≤ m`;
* `powTorsionProjective_biproduct`: a biproduct of objects satisfying the hypothesis satisfies
  it;
* `powTorsionProjective_obj_of_adjunction`: a left adjoint whose right adjoint is additive and
  preserves epimorphisms preserves it; in particular `powTorsionProjective_compactInduction`,
  for compact induction `c-Ind_H^G` from an open subgroup `H`;
* `powTorsionProjective_cokernel_powSMul`, `powSMul_cokernel_powSMul`: the cokernel `P/ℓ^m P`
  of multiplication by `ℓ ^ m` on an object `P` satisfying the hypothesis (for instance a
  projective object) satisfies it and is killed by `ℓ ^ m`. For a free `𝒪[Γ]`-module `P`,
  `P/ℓ^m P` is the free `𝒪/ℓ^m𝒪[Γ]`-module of the same rank; this identification is not
  formalized here.

For `ℓ`-divisible systems of cochain complexes, `TermwisePowTorsionProjective T` states that
every term `(T m) ^ p` satisfies `PowTorsionProjective ℓ m`, the hypothesis of the published
surjectivity lemmas. It is preserved by finite direct sums
(`termwisePowTorsionProjective_biproduct`), by left adjoints as above
(`termwisePowTorsionProjective_map_of_adjunction`) and by compact induction from open subgroups
(`termwisePowTorsionProjective_compactInductionSystem`). For the inverse system of Hom
complexes `m ↦ Hom^•_G(⨁ᵢ c-Ind_{Hᵢ}^G Tᵢ m, W m)` of the published module
`BiproductHomSystem` (for one degree `-i`, the shape of Harris's complexes on p.311 before their
rewriting into (4.10.2)), the degreewise transitions and limit projections are therefore
surjective and the system satisfies the Mittag-Leffler condition in every degree as soon as
every `Tᵢ` satisfies `TermwisePowTorsionProjective`
(`isMittagLeffler_smoothHomComplexSystem_biproduct_compactInduction_eval`).

That Harris's modules `C^j_m(ẽ)^{H_p}` satisfy the hypothesis, and the passage from `C^j_m(ẽ)` to
its `H_p`-invariants, are not formalized here.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w v v' u u'

attribute [local instance] Abelian.hasFiniteBiproducts

namespace DivisibleSystem

section Projective

variable {C : Type u} [Category.{v} C] [Preadditive C] {ℓ m : ℕ}

/-- Projectivity relative to objects killed by `ℓ ^ m` is invariant under isomorphism. -/
lemma powTorsionProjective_of_iso {P Q : C} (e : P ≅ Q) (hP : PowTorsionProjective ℓ m P) :
    PowTorsionProjective ℓ m Q := by
  intro X Y p hp hX g
  obtain ⟨f, hf⟩ := hP p hp hX (e.hom ≫ g)
  exact ⟨e.inv ≫ f, by rw [Category.assoc, hf, Iso.inv_hom_id_assoc]⟩

lemma powTorsionProjective_iff_of_iso {P Q : C} (e : P ≅ Q) :
    PowTorsionProjective ℓ m P ↔ PowTorsionProjective ℓ m Q :=
  ⟨powTorsionProjective_of_iso e, powTorsionProjective_of_iso e.symm⟩

/-- An object projective relative to objects killed by `ℓ ^ m` is projective relative to
objects killed by `ℓ ^ m'` for `m' ≤ m`, since these are killed by `ℓ ^ m`. -/
lemma powTorsionProjective_of_le {m' : ℕ} (h : m' ≤ m) {P : C}
    (hP : PowTorsionProjective ℓ m P) : PowTorsionProjective ℓ m' P := by
  intro X Y p hp hX g
  refine hP p hp ?_ g
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← powSMul_comp_powSMul, hX, zero_comp]

/-- A biproduct of objects projective relative to objects killed by `ℓ ^ m` is projective
relative to objects killed by `ℓ ^ m`: the lifts of the components are assembled by
`biproduct.desc`. -/
lemma powTorsionProjective_biproduct {ι : Type*} (X : ι → C) [HasBiproduct X]
    (hX : ∀ i, PowTorsionProjective ℓ m (X i)) : PowTorsionProjective ℓ m (⨁ X) := by
  intro Y Z p hp hY g
  choose f hf using fun i => hX i p hp hY (biproduct.ι X i ≫ g)
  exact ⟨biproduct.desc f, biproduct.hom_ext' _ _ fun i => by rw [biproduct.ι_desc_assoc, hf]⟩

variable {D : Type u'} [Category.{v'} D] [Preadditive D]

/-- A left adjoint `F` whose right adjoint `G` is additive and preserves epimorphisms sends
objects projective relative to objects killed by `ℓ ^ m` to such objects: `G` carries an
epimorphism `p : X ⟶ Y` with `X` killed by `ℓ ^ m` to such an epimorphism, and a lift of the
adjoint morphism `P ⟶ G Y` along `G p` is adjoint to a lift along `p`. -/
lemma powTorsionProjective_obj_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [G.Additive] [G.PreservesEpimorphisms] {P : C} (hP : PowTorsionProjective ℓ m P) :
    PowTorsionProjective ℓ m (F.obj P) := by
  intro X Y p hp hX g
  have : Epi (G.map p) := G.map_epi p
  obtain ⟨f, hf⟩ := hP (G.map p) this (by rw [← map_powSMul, hX, G.map_zero])
    (adj.homEquiv _ _ g)
  refine ⟨(adj.homEquiv _ _).symm f, ?_⟩
  rw [← adj.homEquiv_naturality_right_symm, hf, Equiv.symm_apply_apply]

/-- The cokernel `P/ℓ^m P` of multiplication by `ℓ ^ m` is killed by `ℓ ^ m`. -/
lemma powSMul_cokernel_powSMul (P : C) [HasCokernel (powSMul ℓ m P)] :
    powSMul ℓ m (cokernel (powSMul ℓ m P)) = 0 :=
  (cancel_epi (cokernel.π (powSMul ℓ m P))).1 (by
    rw [comp_powSMul, cokernel.condition, comp_zero])

/-- The cokernel `P/ℓ^m P` of multiplication by `ℓ ^ m` on an object `P` projective relative to
objects killed by `ℓ ^ m` is projective relative to objects killed by `ℓ ^ m`: a lift
`P ⟶ X` of `P ⟶ P/ℓ^m P ⟶ Y` kills `ℓ ^ m P` because `X` is killed by `ℓ ^ m`, so it factors
through `P/ℓ^m P`. With `powTorsionProjective_of_projective`, this applies to every projective
`P`. -/
lemma powTorsionProjective_cokernel_powSMul {P : C} [HasCokernel (powSMul ℓ m P)]
    (hP : PowTorsionProjective ℓ m P) :
    PowTorsionProjective ℓ m (cokernel (powSMul ℓ m P)) := by
  intro X Y p hp hX g
  obtain ⟨f, hf⟩ := hP p hp hX (cokernel.π _ ≫ g)
  have h0 : powSMul ℓ m P ≫ f = 0 := by rw [← comp_powSMul, hX, comp_zero]
  refine ⟨cokernel.desc _ f h0, (cancel_epi (cokernel.π (powSMul ℓ m P))).1 ?_⟩
  rw [cokernel.π_desc_assoc, hf]

end Projective

section Termwise

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}

/-- Every term `(T m) ^ p` of an `ℓ`-divisible system `T` of cochain complexes is projective
relative to objects killed by `ℓ ^ m`. This is the hypothesis of the published surjectivity and
Mittag-Leffler lemmas for the inverse systems of Hom complexes `homComplexSystem R T W`
(`homComplexSystem_map_f_surjective`, `isMittagLeffler_homComplexSystem_eval`,
`homComplexLimit_π_f_surjective`), Harris 1999, p.312. -/
def TermwisePowTorsionProjective (T : DivisibleSystem (CochainComplex C ℤ) ℓ) : Prop :=
  ∀ m p, PowTorsionProjective ℓ m ((T.obj m).X p)

/-- A finite direct sum of `ℓ`-divisible systems of cochain complexes whose terms are
projective relative to objects killed by `ℓ ^ m` has the same property: the term
`(⨁ᵢ Tᵢ m) ^ p` is isomorphic to `⨁ᵢ (Tᵢ m) ^ p`. -/
lemma termwisePowTorsionProjective_biproduct {ι : Type} [Finite ι]
    (T : ι → DivisibleSystem (CochainComplex C ℤ) ℓ)
    (hT : ∀ i, TermwisePowTorsionProjective (T i)) :
    TermwisePowTorsionProjective (biproduct T) := by
  intro m p
  exact powTorsionProjective_of_iso
    ((HomologicalComplex.eval C (ComplexShape.up ℤ) p).mapBiproduct fun i => (T i).obj m).symm
    (powTorsionProjective_biproduct _ fun i => hT i m p)

variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- An exact left adjoint `F` whose right adjoint `G` is additive and preserves epimorphisms,
applied to the terms of an `ℓ`-divisible system of cochain complexes, preserves the
projectivity of the terms relative to objects killed by `ℓ ^ m`. -/
lemma termwisePowTorsionProjective_map_of_adjunction
    (T : DivisibleSystem (CochainComplex C ℤ) ℓ) {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [G.PreservesEpimorphisms] (hT : TermwisePowTorsionProjective T) :
    TermwisePowTorsionProjective (T.map (F.mapHomologicalComplex (ComplexShape.up ℤ))) :=
  fun m p => powTorsionProjective_obj_of_adjunction adj (hT m p)

end Termwise

end DivisibleSystem

section Smooth

open SupercuspidalExt DivisibleSystem

variable (R : Type u) [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ℓ : ℕ}

/-- Compact induction `c-Ind_H^G` from an open subgroup `H` preserves projectivity relative to
objects killed by `ℓ ^ m`: it is left adjoint to restriction, which is additive and preserves
epimorphisms. -/
lemma powTorsionProjective_compactInduction {H : Subgroup G} (hH : IsOpen (H : Set G)) {m : ℕ}
    {P : SmoothRep.{u, u, u} R H} (hP : PowTorsionProjective ℓ m P) :
    PowTorsionProjective ℓ m ((compactInduction R G H).obj P) :=
  powTorsionProjective_obj_of_adjunction (compactInductionAdjunction R G H hH) hP

/-- Compact induction from an open subgroup, applied to an `ℓ`-divisible system of cochain
complexes of smooth representations, preserves the projectivity of the terms relative to
objects killed by `ℓ ^ m`. -/
lemma termwisePowTorsionProjective_compactInductionSystem {H : Subgroup G}
    (hH : IsOpen (H : Set G)) (T : SmoothRepComplexDivisibleSystem.{u, u, u} R H ℓ)
    (hT : TermwisePowTorsionProjective T) :
    TermwisePowTorsionProjective (compactInductionSystem R hH T) :=
  fun m p => powTorsionProjective_compactInduction R hH (hT m p)

variable {ι : Type} [Finite ι] {H : ι → Subgroup G} (hH : ∀ i, IsOpen (H i : Set G))

/-- The finite direct sum `m ↦ ⨁ᵢ c-Ind_{Hᵢ}^G Tᵢ m` of compact inductions from open
subgroups (the shape of Harris's (4.4.4)) has terms projective relative to objects killed by
`ℓ ^ m` when every `Tᵢ` has. -/
lemma termwisePowTorsionProjective_biproduct_compactInductionSystem
    (T : (i : ι) → SmoothRepComplexDivisibleSystem.{u, u, u} R (H i) ℓ)
    (hT : ∀ i, TermwisePowTorsionProjective (T i)) :
    TermwisePowTorsionProjective
      (DivisibleSystem.biproduct fun i => compactInductionSystem R (hH i) (T i)) :=
  termwisePowTorsionProjective_biproduct _ fun i =>
    termwisePowTorsionProjective_compactInductionSystem R (hH i) (T i) (hT i)

/-- Harris 1999, p.312, surjectivity of the maps (4.10.3), for the inverse system of Hom
complexes `m ↦ Hom^•_G(⨁ᵢ c-Ind_{Hᵢ}^G Tᵢ m, W m)`: its degree-`n` transitions are surjective
when every term `(Tᵢ m) ^ p` is projective relative to objects killed by `ℓ ^ m`. -/
lemma smoothHomComplexSystem_biproduct_compactInduction_map_f_surjective
    (T : (i : ι) → SmoothRepComplexDivisibleSystem.{u, u, u} R (H i) ℓ)
    (hT : ∀ i, TermwisePowTorsionProjective (T i))
    (W : SmoothRepComplexDivisibleSystem.{u, u, u} R G ℓ) {m m' : ℕᵒᵖ} (φ : m ⟶ m') (n : ℤ) :
    Function.Surjective (((smoothHomComplexSystem R G
      (DivisibleSystem.biproduct fun i => compactInductionSystem R (hH i) (T i)) W).map φ).f n) :=
  homComplexSystem_map_f_surjective R _ W
    (termwisePowTorsionProjective_biproduct_compactInductionSystem R hH T hT) φ n

/-- Harris 1999, proof of Proposition 4.10, p.312: the inverse system of Hom complexes
`m ↦ Hom^•_G(⨁ᵢ c-Ind_{Hᵢ}^G Tᵢ m, W m)` satisfies the Mittag-Leffler condition in every degree
when every term `(Tᵢ m) ^ p` is projective relative to objects killed by `ℓ ^ m`. -/
lemma isMittagLeffler_smoothHomComplexSystem_biproduct_compactInduction_eval
    (T : (i : ι) → SmoothRepComplexDivisibleSystem.{u, u, u} R (H i) ℓ)
    (hT : ∀ i, TermwisePowTorsionProjective (T i))
    (W : SmoothRepComplexDivisibleSystem.{u, u, u} R G ℓ) (n : ℤ) :
    (smoothHomComplexSystem R G
        (DivisibleSystem.biproduct fun i => compactInductionSystem R (hH i) (T i)) W ⋙
      HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n ⋙
        forget (ModuleCat.{u} R)).IsMittagLeffler :=
  isMittagLeffler_smoothHomComplexSystem_eval R G _ W
    (termwisePowTorsionProjective_biproduct_compactInductionSystem R hH T hT) n

/-- The degree-`n` components of the limit projections
`lim_m Hom^•_G(⨁ᵢ c-Ind_{Hᵢ}^G Tᵢ m, W m) ⟶ Hom^•_G(⨁ᵢ c-Ind_{Hᵢ}^G Tᵢ m, W m)` are surjective
when every term `(Tᵢ m) ^ p` is projective relative to objects killed by `ℓ ^ m`. -/
lemma smoothHomComplexLimit_biproduct_compactInduction_π_f_surjective
    (T : (i : ι) → SmoothRepComplexDivisibleSystem.{u, u, u} R (H i) ℓ)
    (hT : ∀ i, TermwisePowTorsionProjective (T i))
    (W : SmoothRepComplexDivisibleSystem.{u, u, u} R G ℓ) (m : ℕ) (n : ℤ) :
    Function.Surjective ((limit.π (smoothHomComplexSystem R G
      (DivisibleSystem.biproduct fun i => compactInductionSystem R (hH i) (T i)) W) (op m)).f n) :=
  homComplexLimit_π_f_surjective R _ W
    (termwisePowTorsionProjective_biproduct_compactInductionSystem R hH T hT) m n

end Smooth

end Langlands.Cohomology
