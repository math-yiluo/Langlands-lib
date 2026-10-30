import Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective

/-!
# Free representations over `𝒪/ℓ^m𝒪[Γ]` as representations over `𝒪`

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, proof of
Proposition 4.10, p.312: "Since `C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free
`𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3) are surjective for all `m`."
The published module `FreeTorsionProjective` expresses this freeness for a representation `P`
over `R` (Harris's `𝒪`) as `FreeOverPowQuotient ℓ m P`. This module shows that the predicate
holds exactly for the restrictions of scalars along `R → R ⧸ (ℓ ^ m)` of free representations
over `R ⧸ (ℓ ^ m)`, so that freeness proved over the ring `R ⧸ (ℓ ^ m)` can be fed to the
published Hom-system results.

* `free_asModule_of_iso`: freeness of the module over the group algebra is invariant under
  isomorphism of representations;
* `isTorsionBySet_repRestrictScalars`, `torsionQuotientRepRestrictIso`: the restriction of
  scalars of a representation `Y` over `R ⧸ I` is killed by `I`, and `torsionQuotientRep`
  recovers `Y` from it;
* `powSMul_repRestrictScalars_eq_zero`, `freeOverPowQuotient_repRestrictScalars`: the
  restriction of scalars of a representation over `R ⧸ (ℓ ^ m)` is killed by `ℓ ^ m`, and it
  satisfies `FreeOverPowQuotient ℓ m` when the representation is free over
  `(R ⧸ (ℓ ^ m))[G]`;
* `freeOverPowQuotient_of_iso`, `freeOverPowQuotient_iff`: invariance under isomorphism, and
  the characterization of `FreeOverPowQuotient ℓ m P` as "`P` is isomorphic to the restriction
  of scalars of a free representation over `R ⧸ (ℓ ^ m)`";
* `freeOverPowQuotient_compactInducedInvariants`: the `K`-invariants of a compact induction of
  a trivial representation with coefficients `I →₀ R ⧸ (ℓ ^ m)`, viewed over `R`, satisfy
  `FreeOverPowQuotient ℓ m`.

The module does not prove that Harris's modules `C^j_m(ẽ)^{H_p}` or
`Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are free. The definitions and proofs are ours.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits

universe w u v u'

attribute [local instance] restrictScalarsModule

section AsModule

variable {k : Type u} [CommRing k] {G : Type v} [Monoid G]

/-- Freeness over the group algebra is invariant under isomorphism in `Rep k G`. -/
theorem free_asModule_of_iso {P Q : Rep.{w} k G} (e : P ≅ Q)
    (hP : Module.Free (MonoidAlgebra k G) P.ρ.asModule) :
    Module.Free (MonoidAlgebra k G) Q.ρ.asModule :=
  Module.Free.of_equiv (Induction.asModuleLinearEquiv (Representation.equivOfIso e))

end AsModule

section Quotient

variable {R : Type u} [CommRing R] {I : Ideal R} {G : Type v} [Monoid G]

/-- The restriction of scalars along `R → R ⧸ I` of a representation over `R ⧸ I` is killed
by `I`. -/
lemma isTorsionBySet_repRestrictScalars (Y : Rep.{w} (R ⧸ I) G) :
    Module.IsTorsionBySet R ((repRestrictScalars.{w} R (R ⧸ I) G).obj Y) I := by
  intro x a
  apply (RestrictScalars.addEquiv R (R ⧸ I) Y.V).injective
  refine (RestrictScalars.addEquiv_map_smul R (R ⧸ I) Y.V (a : R) x).trans ?_
  rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 a.2, zero_smul]
  rfl

/-- For a representation `Y` over `R ⧸ I`, the representation over `R ⧸ I` recovered by
`torsionQuotientRep` from its restriction of scalars to `R` is `Y`. -/
def torsionQuotientRepRestrictIso (Y : Rep.{w} (R ⧸ I) G)
    (hY : Module.IsTorsionBySet R ((repRestrictScalars.{w} R (R ⧸ I) G).obj Y) I) :
    torsionQuotientRep ((repRestrictScalars.{w} R (R ⧸ I) G).obj Y) hY ≅ Y :=
  letI := hY.module
  Rep.mkIso (Representation.Equiv.mk
    { toAddEquiv := RestrictScalars.addEquiv R (R ⧸ I) Y.V
      map_smul' := fun s x => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
        rw [RingHom.id_apply, Module.IsTorsionBySet.mk_smul hY]
        exact (RestrictScalars.addEquiv_map_smul R (R ⧸ I) Y.V r x).trans
          (by rw [Ideal.Quotient.algebraMap_eq]; rfl) }
    fun _ => LinearMap.ext fun _ => rfl)

end Quotient

namespace DivisibleSystem

section FreeOverPowQuotient

variable {R : Type u} [CommRing R] {G : Type v} [Monoid G] {ℓ m : ℕ}

/-- Multiplication by `ℓ ^ m` vanishes on the restriction of scalars to `R` of a representation
over `R ⧸ (ℓ ^ m)`. -/
lemma powSMul_repRestrictScalars_eq_zero (Y : Rep.{w} (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G) :
    powSMul ℓ m ((repRestrictScalars.{w} R (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G).obj Y) = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have h := isTorsionBySet_repRestrictScalars Y
  exact (powSMul_hom_apply _ x).trans
    (@h x ⟨_, Ideal.mem_span_singleton_self ((ℓ : R) ^ m)⟩)

/-- A representation over `R ⧸ (ℓ ^ m)` that is free over `(R ⧸ (ℓ ^ m))[G]`, viewed over `R`,
is `FreeOverPowQuotient ℓ m`. -/
theorem freeOverPowQuotient_repRestrictScalars
    (Y : Rep.{w} (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G)
    (hY : Module.Free (MonoidAlgebra (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G) Y.ρ.asModule) :
    FreeOverPowQuotient ℓ m
      ((repRestrictScalars.{w} R (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G).obj Y) :=
  ⟨powSMul_repRestrictScalars_eq_zero Y,
    free_asModule_of_iso (torsionQuotientRepRestrictIso Y _).symm hY⟩

/-- `FreeOverPowQuotient ℓ m` is invariant under isomorphism in `Rep R G`. -/
theorem freeOverPowQuotient_of_iso {P Q : Rep.{w} R G} (e : P ≅ Q)
    (hP : FreeOverPowQuotient ℓ m P) : FreeOverPowQuotient ℓ m Q := by
  obtain ⟨h, hfree⟩ := hP
  have hQ : powSMul ℓ m Q = 0 := by
    calc powSMul ℓ m Q = powSMul ℓ m Q ≫ e.inv ≫ e.hom := by
          rw [Iso.inv_hom_id, Category.comp_id]
      _ = e.inv ≫ powSMul ℓ m P ≫ e.hom := by
          rw [← Category.assoc, ← comp_powSMul, Category.assoc]
      _ = 0 := by rw [h, Limits.zero_comp, Limits.comp_zero]
  let F := repRestrictScalars.{w} R (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G
  exact ⟨hQ, free_asModule_of_iso (F.preimageIso
    (torsionQuotientRepIso P _ ≪≫ e ≪≫ (torsionQuotientRepIso Q _).symm)) hfree⟩

/-- `FreeOverPowQuotient ℓ m P` holds exactly when `P` is isomorphic to the restriction of
scalars to `R` of a representation over `R ⧸ (ℓ ^ m)` that is free over `(R ⧸ (ℓ ^ m))[G]`. -/
theorem freeOverPowQuotient_iff (P : Rep.{w} R G) :
    FreeOverPowQuotient ℓ m P ↔
      ∃ Y : Rep.{w} (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G,
        Module.Free (MonoidAlgebra (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G) Y.ρ.asModule ∧
          Nonempty ((repRestrictScalars.{w} R (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G).obj Y ≅ P) := by
  constructor
  · rintro ⟨h, hfree⟩
    exact ⟨_, hfree, ⟨torsionQuotientRepIso P _⟩⟩
  · rintro ⟨Y, hY, ⟨e⟩⟩
    exact freeOverPowQuotient_of_iso e (freeOverPowQuotient_repRestrictScalars Y hY)

end FreeOverPowQuotient

section CompactInduction

variable {R : Type u} [CommRing R] {ℓ m : ℕ} {G : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {H K : Subgroup G} (hH : IsOpen (H : Set G)) (hHK : H ≤ K) [K.Normal]
  [(H.subgroupOf K).FiniteIndex] (I : Type u')

include hH hHK in
/-- Harris 1999, p.312: with coefficients `I →₀ R ⧸ (ℓ ^ m)`, the `K`-invariants of the compact
induction from `H` of the trivial representation, viewed as a representation of `G ⧸ K` over
`R`, are free over `(R ⧸ (ℓ ^ m))[G ⧸ K]`. -/
theorem freeOverPowQuotient_compactInducedInvariants :
    FreeOverPowQuotient ℓ m
      ((repRestrictScalars R (R ⧸ Ideal.span {((ℓ : R) ^ m)}) (G ⧸ K)).obj
        (Rep.of ((Induction.compactInduced H
          (Representation.trivial (R ⧸ Ideal.span {((ℓ : R) ^ m)}) H
            (I →₀ R ⧸ Ideal.span {((ℓ : R) ^ m)}))).quotientToInvariants K))) :=
  freeOverPowQuotient_repRestrictScalars _
    (Induction.compactInducedInvariants_free (R ⧸ Ideal.span {((ℓ : R) ^ m)}) hH hHK I)

end CompactInduction

end DivisibleSystem

end Langlands.Cohomology
