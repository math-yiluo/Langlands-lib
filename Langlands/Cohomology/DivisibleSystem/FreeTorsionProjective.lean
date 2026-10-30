import Langlands.Cohomology.DivisibleSystem.PowTorsionProjective
import Langlands.Cohomology.DivisibleSystem.ScalarExtension
import Langlands.Representation.Induction.PermutationInvariants

/-!
# Free modules over `𝒪/ℓ^m𝒪[Γ]` are projective relative to objects killed by `ℓ ^ m`

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, proof of
Proposition 4.10, p.312: "Since `C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free
`𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3) are surjective for all `m`."
The published module `HomSurjective` abstracts the freeness used there as the hypothesis
`PowTorsionProjective ℓ m P` on an object `P` of `Rep R Γ`: every morphism from `P` lifts along
epimorphisms whose source is killed by `ℓ ^ m`. This module proves that Harris's freeness implies
this hypothesis.

* `repRestrictScalars_faithful`, `repRestrictScalars_full_of_surjective`,
  `repRestrictScalars_quotient_full`: restriction of scalars of representations along an algebra
  `R → S` is faithful, and full when `algebraMap R S` is surjective, for instance for
  `R → R ⧸ I`;
* `torsionQuotientRep X hX`: a representation `X` over `R` killed by an ideal `I`, as a
  representation over `R ⧸ I` with the same operators; restricting its scalars back to `R`
  gives `X` (`torsionQuotientRepIso`). Every object killed by `ℓ ^ m` is killed by the ideal
  `(ℓ ^ m)` (`isTorsionBySet_of_powSMul_eq_zero`), and so is every quotient of it
  (`isTorsionBySet_of_epi`);
* `powTorsionProjective_repRestrictScalars`: a projective object of `Rep (R ⧸ (ℓ ^ m)) Γ`,
  viewed over `R`, satisfies `PowTorsionProjective ℓ m`. A lifting problem along an epimorphism
  whose source is killed by `ℓ ^ m` lies in the image of restriction of scalars, which is full
  and faithful, and is solved there;
* `projective_of_free_asModule`: a representation whose module over the group algebra `k[Γ]` is
  free is projective in `Rep k Γ`;
* `FreeOverPowQuotient ℓ m P`, Harris's "free `𝒪/ℓ^m𝒪[Γ]`-module" for `𝒪 = R`: `P` is killed
  by `ℓ ^ m`, and its module over the group algebra `(R ⧸ (ℓ ^ m))[Γ]` is free.
  `powTorsionProjective_of_freeOverPowQuotient` derives `PowTorsionProjective ℓ m P` from it
  (through `powTorsionProjective_of_projective_torsionQuotientRep`), and
  `homSystem_map_surjective_of_freeOverPowQuotient`,
  `isMittagLeffler_homSystem_of_freeOverPowQuotient` and
  `towerHomEval_surjective_of_freeOverPowQuotient` restate the published consequences for the
  inverse system `m ↦ Hom_Γ(T m, W m)` of two `ℓ`-divisible systems `T`, `W` of representations;
* `projective_compactInducedInvariants`, `powTorsionProjective_compactInducedInvariants`: for an
  open subgroup `H` of a topological group `G` and a normal subgroup `K ⊇ H` in which `H` has
  finite index, the `K`-invariants of the compact induction from `H` of the trivial
  representation on `I →₀ R ⧸ (ℓ ^ m)`, a free `(R ⧸ (ℓ ^ m))[G ⧸ K]`-module by the published
  `Induction.compactInducedInvariants_free`, satisfy `PowTorsionProjective ℓ m` over `R`.

In Harris's setting `Γ = S(ẽ)/H_p`. The module does not prove that Harris's modules
`C^j_m(ẽ)^{H_p}` are free, and it does not treat his modules `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`. The
definitions and proofs are ours.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w u u' v

attribute [local instance] restrictScalarsModule

section RestrictScalars

variable {R : Type u} [CommRing R] {S : Type u'} [CommRing S] [Algebra R S] (G : Type v)
  [Monoid G]

/-- Restriction of scalars of representations is faithful. -/
instance repRestrictScalars_faithful : (repRestrictScalars.{w} R S G).Faithful where
  map_injective {A B} f g h := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun φ : (repRestrictScalars.{w} R S G).obj A ⟶
        (repRestrictScalars.{w} R S G).obj B =>
      RestrictScalars.addEquiv R S B.V (φ.hom ((RestrictScalars.addEquiv R S A.V).symm x))) h

variable {G}

/-- For `algebraMap R S` surjective, an `R`-linear `G`-equivariant map between restrictions of
scalars of representations over `S` is `S`-linear: the same map, as a morphism of
representations over `S`. -/
def repRestrictScalarsPreimage (hS : Function.Surjective (algebraMap R S)) {A B : Rep.{w} S G}
    (f : (repRestrictScalars.{w} R S G).obj A ⟶ (repRestrictScalars.{w} R S G).obj B) :
    A ⟶ B :=
  Rep.ofHom
    { toFun := fun x =>
        RestrictScalars.addEquiv R S B.V (f.hom ((RestrictScalars.addEquiv R S A.V).symm x))
      map_add' := fun x y =>
        congrArg (RestrictScalars.addEquiv R S B.V)
          (map_add f.hom ((RestrictScalars.addEquiv R S A.V).symm x)
            ((RestrictScalars.addEquiv R S A.V).symm y))
      map_smul' := fun s x => by
        obtain ⟨r, rfl⟩ := hS s
        exact congrArg (RestrictScalars.addEquiv R S B.V)
          (map_smul f.hom r ((RestrictScalars.addEquiv R S A.V).symm x))
      isIntertwining' := fun g => LinearMap.ext fun x =>
        congrArg (RestrictScalars.addEquiv R S B.V)
          (Rep.hom_comm_apply f g ((RestrictScalars.addEquiv R S A.V).symm x)) }

lemma repRestrictScalars_map_preimage (hS : Function.Surjective (algebraMap R S))
    {A B : Rep.{w} S G}
    (f : (repRestrictScalars.{w} R S G).obj A ⟶ (repRestrictScalars.{w} R S G).obj B) :
    (repRestrictScalars.{w} R S G).map (repRestrictScalarsPreimage hS f) = f :=
  Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun _ => rfl

variable (G)

/-- Restriction of scalars along a surjective `algebraMap R S` is full. -/
lemma repRestrictScalars_full_of_surjective (hS : Function.Surjective (algebraMap R S)) :
    (repRestrictScalars.{w} R S G).Full :=
  ⟨fun f => ⟨repRestrictScalarsPreimage hS f, repRestrictScalars_map_preimage hS f⟩⟩

end RestrictScalars

section Quotient

variable {R : Type u} [CommRing R] (I : Ideal R) (G : Type v) [Monoid G]

/-- Restriction of scalars along `R → R ⧸ I` is full. -/
instance repRestrictScalars_quotient_full : (repRestrictScalars.{w} R (R ⧸ I) G).Full :=
  repRestrictScalars_full_of_surjective G (by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective)

variable {I G}

/-- The representation over `R ⧸ I` on a representation `X` over `R` killed by `I`: the same
operators, with `R ⧸ I` acting through `Module.IsTorsionBySet.module`. -/
def torsionQuotientRepresentation (X : Rep.{w} R G) (hX : Module.IsTorsionBySet R X I) :
    letI := hX.module
    Representation (R ⧸ I) G X :=
  letI := hX.module
  { toFun := fun g =>
      { toFun := X.ρ g
        map_add' := map_add (X.ρ g)
        map_smul' := fun s x => by
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
          exact (X.ρ g).map_smul r x }
    map_one' := LinearMap.ext fun x => by simp
    map_mul' := fun g h => LinearMap.ext fun x => by simp }

/-- A representation `X` over `R` killed by an ideal `I`, as a representation over `R ⧸ I`. -/
def torsionQuotientRep (X : Rep.{w} R G) (hX : Module.IsTorsionBySet R X I) :
    Rep.{w} (R ⧸ I) G :=
  letI := hX.module
  Rep.of (torsionQuotientRepresentation X hX)

/-- The restriction of scalars of `torsionQuotientRep X hX` along `R → R ⧸ I` is `X`. -/
def torsionQuotientRepIso (X : Rep.{w} R G) (hX : Module.IsTorsionBySet R X I) :
    (repRestrictScalars.{w} R (R ⧸ I) G).obj (torsionQuotientRep X hX) ≅ X :=
  letI := hX.module
  Rep.mkIso (Representation.Equiv.mk
    { toAddEquiv := RestrictScalars.addEquiv R (R ⧸ I) X.V
      map_smul' := fun r x => by
        rw [RingHom.id_apply]
        exact RestrictScalars.addEquiv_map_smul R (R ⧸ I) X.V r x }
    fun _ => LinearMap.ext fun _ => rfl)

/-- A quotient of a representation killed by `I` is killed by `I`. -/
lemma isTorsionBySet_of_epi {X Y : Rep.{w} R G} (p : X ⟶ Y) [Epi p]
    (hX : Module.IsTorsionBySet R X I) : Module.IsTorsionBySet R Y I := by
  intro y a
  obtain ⟨x, rfl⟩ := (Rep.epi_iff_surjective p).1 inferInstance y
  rw [← map_smul, @hX x a, map_zero]

end Quotient

section Free

variable {k : Type u} [CommRing k] {G : Type v} [Monoid G]

/-- A representation of `G` over `k` whose module over the group algebra `k[G]` is free is a
projective object of `Rep k G`. -/
theorem projective_of_free_asModule (P : Rep.{w} k G)
    (hP : Module.Free (MonoidAlgebra k G) P.ρ.asModule) : Projective P :=
  Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _ <|
    @ModuleCat.projective_of_free _ _ (ModuleCat.of (MonoidAlgebra k G) P.ρ.asModule) _
      (Module.Free.chooseBasis (MonoidAlgebra k G) P.ρ.asModule)

end Free

section PowSMul

variable {R : Type u} [CommRing R] {G : Type v} [Monoid G] {ℓ m : ℕ}

/-- Multiplication by `ℓ ^ m` on a representation over `R` is scalar multiplication by the
element `ℓ ^ m` of `R`. -/
lemma powSMul_hom_apply (X : Rep.{w} R G) (x : X) :
    (powSMul ℓ m X).hom x = ((ℓ : R) ^ m) • x := by
  rw [powSMul, Rep.nsmul_hom]
  change (ℓ ^ m) • (𝟙 X : X ⟶ X).hom x = _
  rw [Rep.hom_id, ← Nat.cast_smul_eq_nsmul R, Nat.cast_pow]
  rfl

/-- A representation on which multiplication by `ℓ ^ m` is zero is killed by the ideal
`(ℓ ^ m)` of `R`. -/
lemma isTorsionBySet_of_powSMul_eq_zero {X : Rep.{w} R G} (h : powSMul ℓ m X = 0) :
    Module.IsTorsionBySet R X (Ideal.span {((ℓ : R) ^ m)}) := by
  intro x a
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 a.2
  rw [← hc, mul_smul, ← powSMul_hom_apply, h]
  exact smul_zero c

end PowSMul

namespace DivisibleSystem

section PowTorsion

variable {R : Type u} [CommRing R] {G : Type v} [Monoid G] {ℓ m : ℕ}

/-- A projective representation of `G` over `R ⧸ (ℓ ^ m)`, viewed as a representation over `R`
by restriction of scalars, is projective relative to objects killed by `ℓ ^ m`. A lifting
problem along an epimorphism `p : X ⟶ Y` with `X` killed by `ℓ ^ m` is transported to
`Rep (R ⧸ (ℓ ^ m)) G` through `torsionQuotientRepIso` and the fullness of restriction of
scalars, and solved there by projectivity. -/
theorem powTorsionProjective_repRestrictScalars
    (P : Rep.{w} (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G) [Projective P] :
    PowTorsionProjective ℓ m
      ((repRestrictScalars.{w} R (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G).obj P) := by
  intro X Y p _ hX g
  let F := repRestrictScalars.{w} R (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G
  have : F.Full := repRestrictScalars_quotient_full _ G
  have : F.Faithful := repRestrictScalars_faithful G
  have hXt := isTorsionBySet_of_powSMul_eq_zero hX
  have hYt := isTorsionBySet_of_epi p hXt
  let eX : F.obj (torsionQuotientRep X hXt) ≅ X := torsionQuotientRepIso X hXt
  let eY : F.obj (torsionQuotientRep Y hYt) ≅ Y := torsionQuotientRepIso Y hYt
  let p' := F.preimage (eX.hom ≫ p ≫ eY.inv)
  have hp' : F.map p' = eX.hom ≫ p ≫ eY.inv := F.map_preimage _
  have : Epi p' := F.epi_of_epi_map (by rw [hp']; infer_instance)
  let f' := Projective.factorThru (F.preimage (g ≫ eY.inv)) p'
  refine ⟨F.map f' ≫ eX.hom, ?_⟩
  have h₁ : F.map f' ≫ F.map p' = g ≫ eY.inv := by
    rw [← F.map_comp, Projective.factorThru_comp, F.map_preimage]
  rw [hp'] at h₁
  calc (F.map f' ≫ eX.hom) ≫ p = (F.map f' ≫ eX.hom ≫ p ≫ eY.inv) ≫ eY.hom := by
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = g := by rw [h₁, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- A representation `P` killed by `ℓ ^ m` whose associated representation over `R ⧸ (ℓ ^ m)` is
projective is projective relative to objects killed by `ℓ ^ m`. -/
theorem powTorsionProjective_of_projective_torsionQuotientRep {P : Rep.{w} R G}
    (h : powSMul ℓ m P = 0)
    [Projective (torsionQuotientRep P (isTorsionBySet_of_powSMul_eq_zero h))] :
    PowTorsionProjective ℓ m P :=
  powTorsionProjective_of_iso (torsionQuotientRepIso P _)
    (powTorsionProjective_repRestrictScalars _)

end PowTorsion

section FreeOverPowQuotient

variable {R : Type u} [CommRing R] {G : Type v} [Monoid G] {ℓ m : ℕ}

variable (ℓ m) in
/-- Harris 1999, p.312, "free `𝒪/ℓ^m𝒪[Γ]`-module": `P` is killed by `ℓ ^ m`, and `P`, as a
module over the group algebra `(R ⧸ (ℓ ^ m))[G]` through `torsionQuotientRep`, is free. -/
def FreeOverPowQuotient (P : Rep.{w} R G) : Prop :=
  ∃ h : powSMul ℓ m P = 0, Module.Free (MonoidAlgebra (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G)
    (torsionQuotientRep P (isTorsionBySet_of_powSMul_eq_zero h)).ρ.asModule

/-- A representation that is free over `(R ⧸ (ℓ ^ m))[G]` is projective relative to objects
killed by `ℓ ^ m`. -/
theorem powTorsionProjective_of_freeOverPowQuotient {P : Rep.{w} R G}
    (hP : FreeOverPowQuotient ℓ m P) : PowTorsionProjective ℓ m P := by
  obtain ⟨h, hfree⟩ := hP
  have := projective_of_free_asModule _ hfree
  exact powTorsionProjective_of_projective_torsionQuotientRep h

variable (T W : DivisibleSystem (Rep.{w} R G) ℓ)

/-- Harris 1999, p.312: the transitions of the inverse system `homSystem R T W` are surjective
when every `T m` is free over `(R ⧸ (ℓ ^ m))[G]`. -/
lemma homSystem_map_surjective_of_freeOverPowQuotient
    (hT : ∀ m, FreeOverPowQuotient ℓ m (T.obj m)) {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective ((homSystem R T W).map φ) :=
  homSystem_map_surjective R T W (fun m => powTorsionProjective_of_freeOverPowQuotient (hT m)) φ

/-- The inverse system `homSystem R T W` satisfies the Mittag-Leffler condition when every
`T m` is free over `(R ⧸ (ℓ ^ m))[G]`. -/
lemma isMittagLeffler_homSystem_of_freeOverPowQuotient
    (hT : ∀ m, FreeOverPowQuotient ℓ m (T.obj m)) :
    (homSystem R T W ⋙ CategoryTheory.forget (ModuleCat.{w} R)).IsMittagLeffler :=
  isMittagLeffler_homSystem R T W fun m => powTorsionProjective_of_freeOverPowQuotient (hT m)

/-- Every morphism `T n ⟶ W n` is the level-`n` component of a morphism of inverse systems
`T.tower ⟶ W.tower` when every `T m` is free over `(R ⧸ (ℓ ^ m))[G]`. -/
lemma towerHomEval_surjective_of_freeOverPowQuotient
    (hT : ∀ m, FreeOverPowQuotient ℓ m (T.obj m)) (n : ℕ) :
    Function.Surjective (towerHomEval R T W n) :=
  towerHomEval_surjective R T W (fun m => powTorsionProjective_of_freeOverPowQuotient (hT m)) n

end FreeOverPowQuotient

section CompactInduction

variable (k : Type u) [CommRing k] {G : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {H K : Subgroup G} (hH : IsOpen (H : Set G)) (hHK : H ≤ K) [K.Normal]
  [(H.subgroupOf K).FiniteIndex] (I : Type u')

include hH hHK in
/-- For an open subgroup `H ≤ K` with `K` normal and `H` of finite index in `K`, the
`K`-invariants of the compact induction from `H` of the trivial representation on `I →₀ k`
form a projective object of `Rep k (G ⧸ K)`. -/
theorem projective_compactInducedInvariants :
    Projective (Rep.of
      ((Induction.compactInduced H (Representation.trivial k H (I →₀ k))).quotientToInvariants
        K)) :=
  projective_of_free_asModule _ (Induction.compactInducedInvariants_free k hH hHK I)

variable {R : Type u} [CommRing R] {ℓ m : ℕ}

include hH hHK in
/-- Harris 1999, p.312: with coefficients `I →₀ R ⧸ (ℓ ^ m)`, the `K`-invariants of the compact
induction from `H` of the trivial representation, viewed as a representation of `G ⧸ K` over
`R`, are projective relative to objects killed by `ℓ ^ m`. -/
theorem powTorsionProjective_compactInducedInvariants :
    PowTorsionProjective ℓ m
      ((repRestrictScalars R (R ⧸ Ideal.span {((ℓ : R) ^ m)}) (G ⧸ K)).obj
        (Rep.of ((Induction.compactInduced H
          (Representation.trivial (R ⧸ Ideal.span {((ℓ : R) ^ m)}) H
            (I →₀ R ⧸ Ideal.span {((ℓ : R) ^ m)}))).quotientToInvariants K))) :=
  haveI := projective_compactInducedInvariants (R ⧸ Ideal.span {((ℓ : R) ^ m)}) hH hHK I
  powTorsionProjective_repRestrictScalars _

end CompactInduction

end DivisibleSystem

end Langlands.Cohomology
