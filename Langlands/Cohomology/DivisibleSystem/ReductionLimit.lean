import Langlands.Cohomology.DivisibleSystem.IHomReduction
import Langlands.Cohomology.DivisibleSystem.InverseLimit
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite.CompletenessProofs

/-!
# The inverse limit of the reductions `L / ℓ ^ m L`

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, §4, p.311: "let
`𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any `m`. Then `𝓛_m` forms an inverse system of `𝒪`-modules"; the proof
of Proposition 4.10 (p.312) passes to the limit over `m` in the spectral sequences (4.9), whose
coefficients are `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)`, and arrives at the integral statement (4.10.4)
with coefficients `𝓛`. The published `reductionTower ℓ L` models the inverse system by the
cokernels `L / ℓ ^ m L` of multiplication by `ℓ ^ m`.

This module identifies the inverse limit of this system, for a representation `L` of a monoid
`G` over a commutative ring `R`:

* `reductionπ_hom_apply_eq_zero_iff`, `reductionπ_hom_apply_eq_iff`: the kernel of the
  projection `L ⟶ L / ℓ ^ m L` is `ℓ ^ m L`, so two elements have the same image exactly when
  they are congruent modulo `(ℓ) ^ m • L`;
* `nonempty_isLimit_reductionCone_iff`, `isIso_limit_lift_reductionCone_iff`: `L`, with the
  projections, is the inverse limit of the `L / ℓ ^ m L` exactly when its underlying `R`-module
  is `ℓ`-adically complete and Hausdorff (`IsAdicComplete`);
* `reductionLimitIso`, `reductionSystemLimitIso`: for such `L`, `lim_m L / ℓ ^ m L ≅ L`;
* `isAdicComplete_of_finite`: over a Noetherian `ℓ`-adically complete ring, every
  representation finite over `R` is `ℓ`-adically complete (from the published NYLL
  `isAdicComplete_of_moduleFinite`).

For `G` a group and carriers in the universe of `R`, the internal Hom `Hom_R(A, -)` preserves
inverse limits, so for `L` complete:

* `ihomReductionLimitIso`, `ihomReductionSystemLimitIso`:
  `lim_m Hom_R(A, L / ℓ ^ m L) ≅ Hom_R(A, L)`, the latter for Harris's system
  `ihomReductionSystem ℓ A L` when `A` is projective over `R`;
* `isAdicComplete_ihom`: for `A` projective over `R`, `Hom_R(A, L)` is again complete;
* `permutationIhomReductionLimitIso`: Harris's case, `A = M[X]` a permutation representation
  with `M` free and `L` finite over a Noetherian `ℓ`-adically complete ring, with the trivial
  action.

That Harris's integral statement arises from these limits is our reading of the proof of
Proposition 4.10; Harris states neither identification. The definitions and proofs are ours.
-/

noncomputable section

namespace Langlands.Cohomology.DivisibleSystem

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v

section Cone

variable {C : Type u} [Category.{v} C] [Abelian C] (ℓ : ℕ) (L : C)

/-- The cone over `reductionTower ℓ L` with vertex `L` formed by the projections
`L ⟶ L / ℓ ^ m L`. -/
@[simps]
def reductionCone : Cone (reductionTower ℓ L) where
  pt := L
  π :=
    { app m := reductionπ ℓ L m.unop
      naturality {_ _} f := (Category.id_comp _).trans (reductionπ_map ℓ L f).symm }

end Cone

section Rep

variable {R : Type u} [CommRing R] {G : Type v} [Monoid G] (ℓ : ℕ) (L : Rep.{w} R G)

/-- The kernel of the projection `L ⟶ L / ℓ ^ m L` is `ℓ ^ m L`. -/
lemma reductionπ_hom_apply_eq_zero_iff (m : ℕ) (x : L) :
    (reductionπ ℓ L m).hom x = 0 ↔ ∃ y : L, ((ℓ : R) ^ m) • y = x := by
  constructor
  · intro hx
    have hex := ((ShortComplex.mk (powSMul ℓ m L) (reductionπ ℓ L m)
        (powSMul_comp_reductionπ ℓ L m)).exact_map_iff_of_faithful
      (forget₂ (Rep.{w} R G) (ModuleCat.{w} R))).mpr
      (ShortComplex.exact_of_g_is_cokernel _ (reductionπIsCokernel ℓ L m))
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex x hx
    exact ⟨y, (powSMul_hom_apply L y).symm.trans hy⟩
  · rintro ⟨y, rfl⟩
    rw [← powSMul_hom_apply]
    exact congrArg (fun f : L ⟶ (reductionTower ℓ L).obj (op m) => f.hom y)
      (powSMul_comp_reductionπ ℓ L m)

/-- Two elements of `L` have the same image in `L / ℓ ^ m L` exactly when they are congruent
modulo `(ℓ) ^ m L`. -/
lemma reductionπ_hom_apply_eq_iff (m : ℕ) (x y : L) :
    (reductionπ ℓ L m).hom x = (reductionπ ℓ L m).hom y ↔
      x ≡ y [SMOD (Ideal.span {(ℓ : R)} ^ m • ⊤ : Submodule R L)] := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists, ← sub_eq_zero, ← map_sub,
    reductionπ_hom_apply_eq_zero_iff]
  simp only [Submodule.mem_top, true_and]

/-- `L` is the inverse limit of the reductions `L / ℓ ^ m L`, via the projections, exactly when
its underlying `R`-module is complete and Hausdorff for the `ℓ`-adic topology. -/
theorem nonempty_isLimit_reductionCone_iff :
    Nonempty (IsLimit (reductionCone ℓ L)) ↔ IsAdicComplete (Ideal.span {(ℓ : R)}) L := by
  let F := forget₂ (Rep.{w} R G) (ModuleCat.{w} R) ⋙ CategoryTheory.forget (ModuleCat.{w} R)
  have : PreservesLimitsOfSize.{0, 0} (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)) :=
    preservesSmallestLimits_of_preservesLimits _
  have : ReflectsLimitsOfSize.{0, 0} (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)) :=
    reflectsSmallestLimits_of_reflectsLimits _
  have : ReflectsLimitsOfShape ℕᵒᵖ (CategoryTheory.forget (ModuleCat.{w} R)) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have e : Nonempty (IsLimit (reductionCone ℓ L)) ↔
      Nonempty (IsLimit (F.mapCone (reductionCone ℓ L))) :=
    ⟨fun ⟨h⟩ => ⟨isLimitOfPreserves F h⟩, fun ⟨h⟩ => ⟨isLimitOfReflects F h⟩⟩
  rw [e, Types.isLimit_iff, isAdicComplete_iff]
  constructor
  · intro h
    refine ⟨⟨fun x hx => ?_⟩, ⟨fun f hf => ?_⟩⟩
    · obtain ⟨y, -, hy⟩ := h _ (Types.sectionOfCone (F.mapCone (reductionCone ℓ L)) (0 : L)).2
      have hxy : x = y := hy x fun j => by
        induction j using Opposite.rec with | op m =>
        exact (reductionπ_hom_apply_eq_iff ℓ L m x 0).2 (hx m)
      exact hxy.trans (hy (0 : L) fun _ => rfl).symm
    · let s : ∀ j : ℕᵒᵖ, (reductionTower ℓ L ⋙ F).obj j :=
        fun j => (reductionπ ℓ L j.unop).hom (f j.unop)
      have hs : s ∈ (reductionTower ℓ L ⋙ F).sections := by
        intro j j' g
        induction j using Opposite.rec with | op m =>
        induction j' using Opposite.rec with | op n =>
        change ((reductionTower ℓ L).map g).hom ((reductionπ ℓ L m).hom (f m)) =
          (reductionπ ℓ L n).hom (f n)
        exact (congrArg (fun φ : L ⟶ _ => φ.hom (f m)) (reductionπ_map ℓ L g)).trans
          ((reductionπ_hom_apply_eq_iff ℓ L n _ _).2 (hf (leOfHom g.unop)).symm)
      obtain ⟨x, hx, -⟩ := h s hs
      exact ⟨x, fun n => (reductionπ_hom_apply_eq_iff ℓ L n _ _).1 (hx (op n)).symm⟩
  · intro hL s hs
    have hsurj : ∀ m : ℕ, Function.Surjective (reductionπ ℓ L m).hom := fun m =>
      (Rep.epi_iff_surjective _).1 inferInstance
    choose g hg using fun m => hsurj m (s (op m))
    have hcomp : ∀ {m n : ℕ}, m ≤ n → (reductionπ ℓ L m).hom (g n) = s (op m) := fun {m n} h =>
      (congrArg (fun φ : L ⟶ _ => φ.hom (g n)) (reductionπ_map ℓ L (homOfLE h).op)).symm.trans
        ((congrArg ((reductionTower ℓ L).map (homOfLE h).op).hom (hg n)).trans
          (hs (homOfLE h).op))
    obtain ⟨x, hx⟩ := hL.2.prec (f := g) fun {m n} h =>
      (reductionπ_hom_apply_eq_iff ℓ L m _ _).1 ((hg m).trans (hcomp h).symm)
    have hx' : ∀ m : ℕ, (reductionπ ℓ L m).hom x = s (op m) := fun m =>
      ((reductionπ_hom_apply_eq_iff ℓ L m _ _).2 (hx m)).symm.trans (hg m)
    refine ⟨x, fun j => hx' j.unop, fun (y : L) hy => (sub_eq_zero.1 ?_ : y = x)⟩
    refine hL.1.haus _ fun m => SModEq.zero.2 (SModEq.sub_mem.1 ?_)
    exact (reductionπ_hom_apply_eq_iff ℓ L m y x).1 ((hy (op m)).trans (hx' m).symm)

/-- The comparison map from `L` to the inverse limit of `L / ℓ ^ m L` is an isomorphism exactly
when `L` is `ℓ`-adically complete. -/
theorem isIso_limit_lift_reductionCone_iff :
    IsIso (limit.lift (reductionTower ℓ L) (reductionCone ℓ L)) ↔
      IsAdicComplete (Ideal.span {(ℓ : R)}) L :=
  ((limit.isLimit _).nonempty_isLimit_iff_isIso_lift).symm.trans
    (nonempty_isLimit_reductionCone_iff ℓ L)

variable {L}

/-- If `L` is `ℓ`-adically complete, the projections exhibit `L` as the inverse limit of
`L / ℓ ^ m L`. -/
def isLimitReductionCone (hL : IsAdicComplete (Ideal.span {(ℓ : R)}) L) :
    IsLimit (reductionCone ℓ L) :=
  ((nonempty_isLimit_reductionCone_iff ℓ L).2 hL).some

/-- For `L` `ℓ`-adically complete, the inverse limit of `L / ℓ ^ m L` is isomorphic to `L`. -/
def reductionLimitIso (hL : IsAdicComplete (Ideal.span {(ℓ : R)}) L) :
    limit (reductionTower ℓ L) ≅ L :=
  (limit.isLimit _).conePointUniqueUpToIso (isLimitReductionCone ℓ hL)

/-- `reductionLimitIso` commutes with the projections. -/
@[reassoc (attr := simp)]
lemma reductionLimitIso_hom_reductionπ (hL : IsAdicComplete (Ideal.span {(ℓ : R)}) L)
    (m : ℕ) :
    (reductionLimitIso ℓ hL).hom ≫ reductionπ ℓ L m = limit.π (reductionTower ℓ L) (op m) :=
  (limit.isLimit _).conePointUniqueUpToIso_hom_comp (isLimitReductionCone ℓ hL) (op m)

/-- For `L` `ℓ`-adically complete, the inverse limit of the reduction system of `L` is
isomorphic to `L`. -/
def reductionSystemLimitIso [Mono (powSMul ℓ 1 L)]
    (hL : IsAdicComplete (Ideal.span {(ℓ : R)}) L) :
    inverseLimit (reductionSystem ℓ L) ≅ L :=
  reductionLimitIso ℓ hL

end Rep

section Finite

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (ℓ : ℕ)
  [IsAdicComplete (Ideal.span {(ℓ : R)}) R] {G : Type v} [Monoid G]

/-- Over a Noetherian ring complete for the `ℓ`-adic topology, a representation that is finite
over `R` is `ℓ`-adically complete. -/
theorem isAdicComplete_of_finite (L : Rep.{w} R G) [Module.Finite R L] :
    IsAdicComplete (Ideal.span {(ℓ : R)}) L :=
  NYLL.ValuationTheory.DiscreteValuationField.isAdicComplete_of_moduleFinite.{u, w} R L _

end Finite

section IHom

variable {R : Type u} [CommRing R] {G : Type v} [Group G] (ℓ : ℕ) (A : Rep.{u} R G)

/-- For representations in the universe of `R`, `Hom_R(A, -)` preserves inverse limits. -/
instance ihom_preservesLimitsOfShape_nat :
    PreservesLimitsOfShape ℕᵒᵖ (Rep.ihom A : Rep.{u} R G ⥤ Rep.{u} R G) :=
  have : PreservesLimitsOfSize.{0, 0} (Rep.ihom A : Rep.{u} R G ⥤ Rep.{u} R G) :=
    (ihom.adjunction A).rightAdjoint_preservesLimits
  inferInstance

variable {L : Rep.{u} R G} (hL : IsAdicComplete (Ideal.span {(ℓ : R)}) L)

/-- If `L` is `ℓ`-adically complete, `Hom_R(A, L)` is the inverse limit of
`Hom_R(A, L / ℓ ^ m L)`, via composition with the projections. -/
def isLimitIhomReductionCone : IsLimit ((Rep.ihom A).mapCone (reductionCone ℓ L)) :=
  isLimitOfPreserves (Rep.ihom A) (isLimitReductionCone ℓ hL)

/-- For `L` `ℓ`-adically complete, `lim_m Hom_R(A, L / ℓ ^ m L) ≅ Hom_R(A, L)`. -/
def ihomReductionLimitIso :
    limit (reductionTower ℓ L ⋙ Rep.ihom A) ≅ (Rep.ihom A).obj L :=
  (limit.isLimit _).conePointUniqueUpToIso (isLimitIhomReductionCone ℓ A hL)

/-- `ihomReductionLimitIso` commutes with the projections. -/
@[reassoc (attr := simp)]
lemma ihomReductionLimitIso_hom_map_reductionπ (m : ℕ) :
    (ihomReductionLimitIso ℓ A hL).hom ≫ (Rep.ihom A).map (reductionπ ℓ L m) =
      limit.π (reductionTower ℓ L ⋙ Rep.ihom A) (op m) :=
  (limit.isLimit _).conePointUniqueUpToIso_hom_comp (isLimitIhomReductionCone ℓ A hL) (op m)

/-- For `A` projective over `R` and `L` `ℓ`-adically complete, the inverse limit of Harris's
system `m ↦ Hom_R(A, L / ℓ ^ m L)` is isomorphic to `Hom_R(A, L)`. -/
def ihomReductionSystemLimitIso [Module.Projective R A] [Mono (powSMul ℓ 1 L)] :
    inverseLimit (ihomReductionSystem ℓ A L) ≅ (Rep.ihom A).obj L :=
  ihomReductionLimitIso ℓ A hL

include hL in
/-- For `A` projective over `R`, if `L` is `ℓ`-adically complete, so is `Hom_R(A, L)`. -/
theorem isAdicComplete_ihom [Module.Projective R A] :
    IsAdicComplete (Ideal.span {(ℓ : R)}) ((Rep.ihom A).obj L) := by
  refine (nonempty_isLimit_reductionCone_iff ℓ ((Rep.ihom A).obj L)).1 ⟨?_⟩
  refine (IsLimit.postcomposeHomEquiv (ihomReductionTowerIso ℓ A L) _).1 ?_
  refine IsLimit.ofIsoLimit (isLimitIhomReductionCone ℓ A hL) (Cone.ext (Iso.refl _) ?_)
  intro m
  induction m using Opposite.rec with | op m =>
  exact (Category.id_comp _).trans (reductionπ_ihomReductionIso_hom ℓ A L m).symm

end IHom

section Permutation

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (ℓ : ℕ)
  [IsAdicComplete (Ideal.span {(ℓ : R)}) R] {G : Type v} [Group G] {X M L : Type u}
  [MulAction G X] [AddCommGroup M] [Module R M] [Module.Free R M] [AddCommGroup L] [Module R L]
  [Module.Finite R L]

/-- Harris's modules `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` in the limit: over a Noetherian `ℓ`-adically
complete ring `R`, for `M` free and `L` finite over `R` (both with the trivial action), the
inverse limit of `Hom_R(M[X], L / ℓ ^ m L)` is isomorphic to `Hom_R(M[X], L)`. -/
def permutationIhomReductionLimitIso :
    limit (reductionTower ℓ (Rep.of (Representation.trivial R G L)) ⋙
        Rep.ihom (Rep.of (Induction.permutation R G X M))) ≅
      (Rep.ihom (Rep.of (Induction.permutation R G X M))).obj
        (Rep.of (Representation.trivial R G L)) :=
  ihomReductionLimitIso ℓ _ (isAdicComplete_of_finite ℓ _)

end Permutation

end Langlands.Cohomology.DivisibleSystem
