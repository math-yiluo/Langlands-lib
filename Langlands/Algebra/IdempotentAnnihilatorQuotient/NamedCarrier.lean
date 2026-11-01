import Langlands.Algebra.NonUnitalModuleKernels
import Langlands.Algebra.NondegenerateModuleAdditive

/-!
# The annihilator of `eA` and the quotient functor `M ↦ M_e`

Renard (9 July 2026), I.3.2, printed p. 20: for an idempotent `e`,
`F(eA,M) = {m | eA·m = 0}` and `M_e = M/F(eA,M)`. The ambient construction works for
every nonunital ring and every original additive action; no unit law, nondegeneracy or
idempotented-ring hypothesis is used. The quotient reuses the published
integer-compatible quotient, its `mapQ` and its `liftQ`.
-/

set_option autoImplicit false

open CategoryTheory

namespace Langlands.Algebra

universe uA uM uN uP

namespace NonUnitalSubmodule

variable {A : Type uA} [NonUnitalRing A]

section Annihilator

variable (e : Idempotent A) (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]

/-- Renard's `F(eA,M)`: the vectors killed by every element `e * a` of the right ideal `eA`. -/
def idempotentAnnihilator : NonUnitalSubmodule A M where
  carrier := {m | ∀ a : A, ((e : A) * a) • m = 0}
  zero_mem' a := smul_zero ((e : A) * a)
  add_mem' {m n} hm hn a := by
    change ((e : A) * a) • (m + n) = 0
    rw [smul_add, hm a, hn a, add_zero]
  neg_mem' {m} hm a := by
    change ((e : A) * a) • (-m) = 0
    rw [smul_neg, hm a, neg_zero]
  smul_mem' b {m} hm a := by
    rw [← mul_smul, mul_assoc]
    exact hm (a * b)

variable {e M}

@[simp] theorem mem_idempotentAnnihilator {m : M} :
    m ∈ idempotentAnnihilator e M ↔ ∀ a : A, ((e : A) * a) • m = 0 := Iff.rfl

theorem zero_mem_idempotentAnnihilator : (0 : M) ∈ idempotentAnnihilator e M :=
  (idempotentAnnihilator e M).zero_mem'

theorem add_mem_idempotentAnnihilator {m n : M} (hm : m ∈ idempotentAnnihilator e M)
    (hn : n ∈ idempotentAnnihilator e M) : m + n ∈ idempotentAnnihilator e M :=
  (idempotentAnnihilator e M).add_mem' hm hn

theorem neg_mem_idempotentAnnihilator {m : M} (hm : m ∈ idempotentAnnihilator e M) :
    -m ∈ idempotentAnnihilator e M :=
  (idempotentAnnihilator e M).neg_mem' hm

/-- Stability under the original action. -/
theorem smul_mem_idempotentAnnihilator (b : A) {m : M}
    (hm : m ∈ idempotentAnnihilator e M) : b • m ∈ idempotentAnnihilator e M :=
  (idempotentAnnihilator e M).smul_mem' b hm

/-- Vectors of `F(eA,M)` are killed by `e` itself, using `e * e = e`. -/
theorem idempotent_smul_eq_zero_of_mem {m : M} (hm : m ∈ idempotentAnnihilator e M) :
    (e : A) • m = 0 := by
  have h := hm (e : A)
  rwa [e.property.eq] at h

/-- `F(eA,M)` is the largest original stable subgroup killed by `e`. -/
theorem le_idempotentAnnihilator_iff (S : NonUnitalSubmodule A M) :
    S ≤ idempotentAnnihilator e M ↔ ∀ m ∈ S, (e : A) • m = 0 := by
  constructor
  · intro h m hm
    exact idempotent_smul_eq_zero_of_mem (h hm)
  · intro h m hm a
    rw [mul_smul]
    exact h (a • m) (S.smul_mem' a hm)

/-- `F(eA,M)` is all of `M` exactly when `e` acts by zero on `M`. -/
theorem coe_idempotentAnnihilator_eq_univ_iff :
    (idempotentAnnihilator e M : Set M) = Set.univ ↔ ∀ m : M, (e : A) • m = 0 := by
  constructor
  · intro h m
    apply idempotent_smul_eq_zero_of_mem
    change m ∈ (idempotentAnnihilator e M : Set M)
    rw [h]
    exact Set.mem_univ m
  · intro h
    apply Set.eq_univ_of_forall
    intro m a
    rw [mul_smul]
    exact h (a • m)

/-- For the zero idempotent the annihilator is all of `M`. -/
theorem coe_idempotentAnnihilator_eq_univ_of_val_eq_zero (he : (e : A) = 0) :
    (idempotentAnnihilator e M : Set M) = Set.univ :=
  coe_idempotentAnnihilator_eq_univ_iff.2 fun m => by
    rw [he]
    exact NonUnitalModule.zero_smul m

/-- On a zero carrier the annihilator is all of `M`. -/
theorem coe_idempotentAnnihilator_eq_univ_of_subsingleton [Subsingleton M] :
    (idempotentAnnihilator e M : Set M) = Set.univ :=
  coe_idempotentAnnihilator_eq_univ_iff.2 fun _ => Subsingleton.elim _ _

end Annihilator

/-- For the zero original action the annihilator is all of `M`. -/
theorem coe_idempotentAnnihilator_zero_action (e : Idempotent A) (M : Type uM)
    [AddCommGroup M] :
    (letI : NonUnitalModule A M := NonUnitalModule.zero
     (idempotentAnnihilator e M : Set M)) = Set.univ :=
  letI : NonUnitalModule A M := NonUnitalModule.zero
  coe_idempotentAnnihilator_eq_univ_iff.2 fun _ => rfl

end NonUnitalSubmodule

open NonUnitalSubmodule

section Quotient

variable {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
  (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]

/-- Renard's `M_e = M/F(eA,M)`: the published quotient by the canonical integer-compatible
form of `F(eA,M)`. A separate name keeps every competing action off this carrier. -/
def annihilatorQuotientCarrier : Type uM :=
  M ⧸ (idempotentAnnihilator e M).toIntCompatible.toSubmodule

/-- The inherited quotient additive group. -/
instance annihilatorQuotientAddCommGroup : AddCommGroup (annihilatorQuotientCarrier e M) :=
  inferInstanceAs (AddCommGroup (M ⧸ (idempotentAnnihilator e M).toIntCompatible.toSubmodule))

/-- The published quotient action of the original action; no unit law is involved. -/
instance annihilatorQuotientModule : NonUnitalModule A (annihilatorQuotientCarrier e M) :=
  (idempotentAnnihilator e M).toIntCompatible.quotientNonUnitalModule

theorem annihilatorQuotientCarrier_eq :
    annihilatorQuotientCarrier e M =
      (M ⧸ (idempotentAnnihilator e M).toIntCompatible.toSubmodule) := rfl

theorem annihilatorQuotientAddCommGroup_eq :
    annihilatorQuotientAddCommGroup e M =
      (Submodule.Quotient.addCommGroup (idempotentAnnihilator e M).toIntCompatible.toSubmodule :
        AddCommGroup (M ⧸ (idempotentAnnihilator e M).toIntCompatible.toSubmodule)) := rfl

theorem annihilatorQuotientModule_eq :
    annihilatorQuotientModule e M =
      (idempotentAnnihilator e M).toIntCompatible.quotientNonUnitalModule := rfl

/-- The published quotient projection, as an original additive intertwiner. -/
def annihilatorQuotientProjection : NonUnitalModuleHom A M (annihilatorQuotientCarrier e M) :=
  (idempotentAnnihilator e M).toIntCompatible.mkQNonUnitalModuleHom

variable {M}

@[simp] theorem annihilatorQuotientProjection_apply (m : M) :
    annihilatorQuotientProjection e M m =
      (Submodule.Quotient.mk m : M ⧸ (idempotentAnnihilator e M).toIntCompatible.toSubmodule) :=
  rfl

theorem annihilatorQuotientProjection_toAddMonoidHom :
    (annihilatorQuotientProjection e M).toAddMonoidHom =
      ((idempotentAnnihilator e M).toIntCompatible.toSubmodule.mkQ).toAddMonoidHom := rfl

/-- The quotient action on representatives is the original action. -/
theorem annihilatorQuotient_smul_projection (a : A) (m : M) :
    (annihilatorQuotientModule e M).smul a (annihilatorQuotientProjection e M m) =
      annihilatorQuotientProjection e M (a • m) := rfl

theorem smul_annihilatorQuotientProjection (a : A) (m : M) :
    a • annihilatorQuotientProjection e M m = annihilatorQuotientProjection e M (a • m) := rfl

theorem annihilatorQuotientProjection_surjective :
    Function.Surjective (annihilatorQuotientProjection e M) :=
  Submodule.Quotient.mk_surjective _

/-- A representative projects to zero exactly when it lies in `F(eA,M)`. -/
@[simp] theorem annihilatorQuotientProjection_eq_zero_iff (m : M) :
    annihilatorQuotientProjection e M m = 0 ↔ m ∈ idempotentAnnihilator e M :=
  Submodule.Quotient.mk_eq_zero _

/-- The published kernel of the projection is exactly `F(eA,M)`. -/
theorem kernelSubmodule_annihilatorQuotientProjection :
    (annihilatorQuotientProjection e M).kernelSubmodule = idempotentAnnihilator e M :=
  SetLike.ext fun m => annihilatorQuotientProjection_eq_zero_iff e m

/-- Two maps out of `M_e` agreeing on all representatives are equal. -/
theorem annihilatorQuotient_hom_ext {P : Type uP} [AddCommGroup P] [NonUnitalModule A P]
    {f g : NonUnitalModuleHom A (annihilatorQuotientCarrier e M) P}
    (h : f.comp (annihilatorQuotientProjection e M) = g.comp (annihilatorQuotientProjection e M)) :
    f = g := by
  apply NonUnitalModuleHom.ext
  intro x
  obtain ⟨m, rfl⟩ := annihilatorQuotientProjection_surjective e x
  exact congrArg (fun k : NonUnitalModuleHom A M P => k m) h

/-- `M_e` is trivial exactly when `e` acts by zero on `M`. -/
theorem annihilatorQuotient_subsingleton_iff :
    Subsingleton (annihilatorQuotientCarrier e M) ↔ ∀ m : M, (e : A) • m = 0 := by
  rw [← coe_idempotentAnnihilator_eq_univ_iff]
  constructor
  · intro _
    apply Set.eq_univ_of_forall
    intro m
    exact (annihilatorQuotientProjection_eq_zero_iff e m).1 (Subsingleton.elim _ _)
  · intro h
    constructor
    intro x y
    obtain ⟨m, rfl⟩ := annihilatorQuotientProjection_surjective e x
    obtain ⟨n, rfl⟩ := annihilatorQuotientProjection_surjective e y
    have hm : m ∈ (idempotentAnnihilator e M : Set M) := h ▸ Set.mem_univ m
    have hn : n ∈ (idempotentAnnihilator e M : Set M) := h ▸ Set.mem_univ n
    rw [(annihilatorQuotientProjection_eq_zero_iff e m).2 hm,
      (annihilatorQuotientProjection_eq_zero_iff e n).2 hn]

/-- For the zero idempotent the quotient is trivial. -/
theorem annihilatorQuotient_subsingleton_of_val_eq_zero (he : (e : A) = 0) :
    Subsingleton (annihilatorQuotientCarrier e M) :=
  (annihilatorQuotient_subsingleton_iff e).2 fun m => by
    rw [he]
    exact NonUnitalModule.zero_smul m

/-- The quotient of a zero carrier is trivial. -/
instance annihilatorQuotient_subsingleton [Subsingleton M] :
    Subsingleton (annihilatorQuotientCarrier e M) :=
  (annihilatorQuotient_subsingleton_iff e).2 fun _ => Subsingleton.elim _ _

/-- The quotient of a nondegenerate module is nondegenerate: a lifted representative
keeps its fixing idempotent. -/
theorem annihilatorQuotient_isNondegenerate (hM : IsNondegenerate A M) :
    IsNondegenerate A (annihilatorQuotientCarrier e M) := by
  intro x
  obtain ⟨m, rfl⟩ := annihilatorQuotientProjection_surjective e x
  obtain ⟨f, hf⟩ := hM m
  exact ⟨f, by rw [smul_annihilatorQuotientProjection, hf]⟩

end Quotient

/-- For the zero original action the quotient is trivial. -/
theorem annihilatorQuotient_subsingleton_zero_action {A : Type uA} [NonUnitalRing A]
    (e : Idempotent A) (M : Type uM) [AddCommGroup M] :
    letI : NonUnitalModule A M := NonUnitalModule.zero
    Subsingleton (annihilatorQuotientCarrier e M) :=
  letI : NonUnitalModule A M := NonUnitalModule.zero
  (annihilatorQuotient_subsingleton_iff e).2 fun _ => rfl

namespace NonUnitalModuleHom

variable {A : Type uA} [NonUnitalRing A] (e : Idempotent A)
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]
  {P : Type uP} [AddCommGroup P] [NonUnitalModule A P]

/-- Every original intertwiner carries `F(eA,M)` into `F(eA,N)`. -/
theorem map_mem_idempotentAnnihilator (f : NonUnitalModuleHom A M N) {m : M}
    (hm : m ∈ idempotentAnnihilator e M) : f m ∈ idempotentAnnihilator e N := by
  intro a
  rw [← f.map_smul, hm a, f.map_zero]

/-- The same containment, in the form used by the published `mapQ`. -/
theorem idempotentAnnihilator_le_comap (f : NonUnitalModuleHom A M N) :
    (idempotentAnnihilator e M).toIntCompatible ≤
      (idempotentAnnihilator e N).toIntCompatible.comap f.toIntLinearIntertwiner :=
  fun _ hm => f.map_mem_idempotentAnnihilator e hm

/-- The induced map `M_e → N_e`: the published `mapQ` of the canonical integer-linear form. -/
def annihilatorQuotientMap (f : NonUnitalModuleHom A M N) :
    NonUnitalModuleHom A (annihilatorQuotientCarrier e M) (annihilatorQuotientCarrier e N) :=
  (f.toIntLinearIntertwiner.mapQ (idempotentAnnihilator e M).toIntCompatible
    (idempotentAnnihilator e N).toIntCompatible (f.idempotentAnnihilator_le_comap e)).toNonUnitalModuleHom

@[simp] theorem annihilatorQuotientMap_apply_projection (f : NonUnitalModuleHom A M N) (m : M) :
    f.annihilatorQuotientMap e (annihilatorQuotientProjection e M m) =
      annihilatorQuotientProjection e N (f m) := rfl

/-- The underlying additive map is Mathlib's `Submodule.mapQ` of the integer-linear map. -/
theorem annihilatorQuotientMap_toAddMonoidHom (f : NonUnitalModuleHom A M N) :
    (f.annihilatorQuotientMap e).toAddMonoidHom =
      ((idempotentAnnihilator e M).toIntCompatible.toSubmodule.mapQ
        (idempotentAnnihilator e N).toIntCompatible.toSubmodule
        f.toAddMonoidHom.toIntLinearMap (f.idempotentAnnihilator_le_comap e)).toAddMonoidHom :=
  rfl

/-- Naturality of the quotient projections. -/
theorem annihilatorQuotientMap_comp_projection (f : NonUnitalModuleHom A M N) :
    (f.annihilatorQuotientMap e).comp (annihilatorQuotientProjection e M) =
      (annihilatorQuotientProjection e N).comp f := rfl

@[simp] theorem annihilatorQuotientMap_id :
    (id A M).annihilatorQuotientMap e = id A (annihilatorQuotientCarrier e M) :=
  annihilatorQuotient_hom_ext e rfl

theorem annihilatorQuotientMap_comp (g : NonUnitalModuleHom A N P)
    (f : NonUnitalModuleHom A M N) :
    (g.comp f).annihilatorQuotientMap e =
      (g.annihilatorQuotientMap e).comp (f.annihilatorQuotientMap e) :=
  annihilatorQuotient_hom_ext e rfl

@[simp] theorem annihilatorQuotientMap_zero :
    (0 : NonUnitalModuleHom A M N).annihilatorQuotientMap e = 0 := by
  apply annihilatorQuotient_hom_ext e
  apply NonUnitalModuleHom.ext
  intro m
  exact (annihilatorQuotientProjection e N).map_zero

@[simp] theorem annihilatorQuotientMap_add (f g : NonUnitalModuleHom A M N) :
    (f + g).annihilatorQuotientMap e = f.annihilatorQuotientMap e + g.annihilatorQuotientMap e := by
  apply annihilatorQuotient_hom_ext e
  apply NonUnitalModuleHom.ext
  intro m
  exact (annihilatorQuotientProjection e N).map_add (f m) (g m)

@[simp] theorem annihilatorQuotientMap_neg (f : NonUnitalModuleHom A M N) :
    (-f).annihilatorQuotientMap e = -f.annihilatorQuotientMap e := by
  apply annihilatorQuotient_hom_ext e
  apply NonUnitalModuleHom.ext
  intro m
  exact (annihilatorQuotientProjection e N).toAddMonoidHom.map_neg (f m)

/-- Descent of an original intertwiner killing `F(eA,M)`: the published `liftQ`. -/
def annihilatorQuotientDesc (g : NonUnitalModuleHom A M P)
    (h : idempotentAnnihilator e M ≤ g.kernelSubmodule) :
    NonUnitalModuleHom A (annihilatorQuotientCarrier e M) P :=
  (g.toIntLinearIntertwiner.liftQ (idempotentAnnihilator e M).toIntCompatible h).toNonUnitalModuleHom

@[simp] theorem annihilatorQuotientDesc_apply_projection (g : NonUnitalModuleHom A M P)
    (h : idempotentAnnihilator e M ≤ g.kernelSubmodule) (m : M) :
    g.annihilatorQuotientDesc e h (annihilatorQuotientProjection e M m) = g m := rfl

/-- The underlying additive map is Mathlib's `Submodule.liftQ` of the integer-linear map. -/
theorem annihilatorQuotientDesc_toAddMonoidHom (g : NonUnitalModuleHom A M P)
    (h : idempotentAnnihilator e M ≤ g.kernelSubmodule) :
    (g.annihilatorQuotientDesc e h).toAddMonoidHom =
      ((idempotentAnnihilator e M).toIntCompatible.toSubmodule.liftQ
        g.toAddMonoidHom.toIntLinearMap h).toAddMonoidHom := rfl

/-- Factorization through the quotient projection. -/
@[simp] theorem annihilatorQuotientDesc_comp_projection (g : NonUnitalModuleHom A M P)
    (h : idempotentAnnihilator e M ≤ g.kernelSubmodule) :
    (g.annihilatorQuotientDesc e h).comp (annihilatorQuotientProjection e M) = g := rfl

/-- Uniqueness of the factorization. -/
theorem annihilatorQuotientDesc_unique (g : NonUnitalModuleHom A M P)
    (h : idempotentAnnihilator e M ≤ g.kernelSubmodule)
    (l : NonUnitalModuleHom A (annihilatorQuotientCarrier e M) P)
    (hl : l.comp (annihilatorQuotientProjection e M) = g) :
    l = g.annihilatorQuotientDesc e h :=
  annihilatorQuotient_hom_ext e hl

/-- The descent hypothesis is necessary: any map through `M_e` kills `F(eA,M)`. -/
theorem idempotentAnnihilator_le_kernelSubmodule_comp
    (l : NonUnitalModuleHom A (annihilatorQuotientCarrier e M) P) :
    idempotentAnnihilator e M ≤ (l.comp (annihilatorQuotientProjection e M)).kernelSubmodule := by
  intro m hm
  change l (annihilatorQuotientProjection e M m) = 0
  rw [(annihilatorQuotientProjection_eq_zero_iff e m).2 hm, l.map_zero]

end NonUnitalModuleHom

namespace NonUnitalModuleCat

variable {A : Type uA} [NonUnitalRing A] (e : Idempotent A)

/-- The additive endofunctor `M ↦ M_e` on all original modules. -/
def annihilatorQuotientFunctor : NonUnitalModuleCat.{uA, uM} A ⥤ NonUnitalModuleCat.{uA, uM} A where
  obj M := of A (annihilatorQuotientCarrier e M)
  map f := NonUnitalModuleHom.annihilatorQuotientMap e f
  map_id _ := NonUnitalModuleHom.annihilatorQuotientMap_id e
  map_comp f g := NonUnitalModuleHom.annihilatorQuotientMap_comp e g f

@[simp] theorem annihilatorQuotientFunctor_obj (M : NonUnitalModuleCat.{uA, uM} A) :
    (annihilatorQuotientFunctor e).obj M = of A (annihilatorQuotientCarrier e M) := rfl

theorem annihilatorQuotientFunctor_obj_carrier (M : NonUnitalModuleCat.{uA, uM} A) :
    ((annihilatorQuotientFunctor e).obj M : Type uM) =
      (M ⧸ (idempotentAnnihilator e M).toIntCompatible.toSubmodule) := rfl

@[simp] theorem annihilatorQuotientFunctor_map {M N : NonUnitalModuleCat.{uA, uM} A}
    (f : M ⟶ N) :
    (annihilatorQuotientFunctor e).map f = NonUnitalModuleHom.annihilatorQuotientMap e f := rfl

instance annihilatorQuotientFunctor_additive :
    (annihilatorQuotientFunctor.{uA, uM} e).Additive where
  map_add := NonUnitalModuleHom.annihilatorQuotientMap_add e _ _

/-- The quotient projections, natural in the original module. -/
def annihilatorQuotientπ : 𝟭 (NonUnitalModuleCat.{uA, uM} A) ⟶ annihilatorQuotientFunctor e where
  app M := annihilatorQuotientProjection e M
  naturality _ _ f := (NonUnitalModuleHom.annihilatorQuotientMap_comp_projection e f).symm

@[simp] theorem annihilatorQuotientπ_app (M : NonUnitalModuleCat.{uA, uM} A) :
    (annihilatorQuotientπ e).app M = annihilatorQuotientProjection e M := rfl

/-- The restriction to nondegenerate modules, lifted through the published full subcategory. -/
def nondegenerateAnnihilatorQuotientFunctor :
    NondegenerateModuleCat.{uA, uM} A ⥤ NondegenerateModuleCat.{uA, uM} A :=
  (nondegenerateProperty A).lift (nondegenerateInclusion A ⋙ annihilatorQuotientFunctor e)
    fun M => annihilatorQuotient_isNondegenerate e M.property

@[simp] theorem nondegenerateAnnihilatorQuotientFunctor_obj_obj
    (M : NondegenerateModuleCat.{uA, uM} A) :
    ((nondegenerateAnnihilatorQuotientFunctor e).obj M).obj =
      (annihilatorQuotientFunctor e).obj M.obj := rfl

@[simp] theorem nondegenerateAnnihilatorQuotientFunctor_map_hom
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) :
    ((nondegenerateAnnihilatorQuotientFunctor e).map f).hom =
      NonUnitalModuleHom.annihilatorQuotientMap e f.hom := rfl

/-- The nondegenerate functor followed by the published inclusion is the ambient functor
after the inclusion. -/
theorem nondegenerateAnnihilatorQuotientFunctor_comp_inclusion :
    nondegenerateAnnihilatorQuotientFunctor.{uA, uM} e ⋙ nondegenerateInclusion A =
      nondegenerateInclusion A ⋙ annihilatorQuotientFunctor e := rfl

/-- The same relation as Mathlib's canonical isomorphism of the lift. -/
def nondegenerateAnnihilatorQuotientFunctorCompInclusionIso :
    nondegenerateAnnihilatorQuotientFunctor.{uA, uM} e ⋙ nondegenerateInclusion A ≅
      nondegenerateInclusion A ⋙ annihilatorQuotientFunctor e :=
  (nondegenerateProperty A).liftCompιIso _ _

/-- Additivity, from Mathlib's instance for lifts of additive functors. -/
instance nondegenerateAnnihilatorQuotientFunctor_additive :
    (nondegenerateAnnihilatorQuotientFunctor.{uA, uM} e).Additive :=
  Functor.instAdditiveFullSubcategoryLift
    (nondegenerateInclusion A ⋙ annihilatorQuotientFunctor e) (nondegenerateProperty A)
    fun M => annihilatorQuotient_isNondegenerate e M.property

/-- The quotient projections of nondegenerate modules, natural in the module. -/
def nondegenerateAnnihilatorQuotientπ :
    𝟭 (NondegenerateModuleCat.{uA, uM} A) ⟶ nondegenerateAnnihilatorQuotientFunctor e where
  app M := ObjectProperty.homMk (annihilatorQuotientProjection e M.obj)
  naturality _ _ f := by
    apply ObjectProperty.hom_ext
    exact (NonUnitalModuleHom.annihilatorQuotientMap_comp_projection e f.hom).symm

@[simp] theorem nondegenerateAnnihilatorQuotientπ_app_hom
    (M : NondegenerateModuleCat.{uA, uM} A) :
    ((nondegenerateAnnihilatorQuotientπ e).app M).hom = (annihilatorQuotientπ e).app M.obj := rfl

end NonUnitalModuleCat

/-! Complete unapplied interfaces, independent universes and the selected actions. -/

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) → (M : Type uM) →
    [AddCommGroup M] → [NonUnitalModule A M] → NonUnitalSubmodule A M :=
  @NonUnitalSubmodule.idempotentAnnihilator.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) → (M : Type uM) →
    [AddCommGroup M] → [NonUnitalModule A M] →
    NonUnitalModule A (annihilatorQuotientCarrier e M) :=
  @annihilatorQuotientModule.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) → (M : Type uM) →
    [AddCommGroup M] → [NonUnitalModule A M] →
    NonUnitalModuleHom A M (annihilatorQuotientCarrier e M) :=
  @annihilatorQuotientProjection.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule A N] →
    NonUnitalModuleHom A M N →
      NonUnitalModuleHom A (annihilatorQuotientCarrier e M) (annihilatorQuotientCarrier e N) :=
  @NonUnitalModuleHom.annihilatorQuotientMap.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    {P : Type uP} → [AddCommGroup P] → [NonUnitalModule A P] →
    (g : NonUnitalModuleHom A M P) → idempotentAnnihilator e M ≤ g.kernelSubmodule →
      NonUnitalModuleHom A (annihilatorQuotientCarrier e M) P :=
  @NonUnitalModuleHom.annihilatorQuotientDesc.{uA, uM, uP}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    NonUnitalModuleCat.{uA, uM} A ⥤ NonUnitalModuleCat.{uA, uM} A :=
  @NonUnitalModuleCat.annihilatorQuotientFunctor.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    (NonUnitalModuleCat.annihilatorQuotientFunctor.{uA, uM} e).Additive :=
  @NonUnitalModuleCat.annihilatorQuotientFunctor_additive.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    NondegenerateModuleCat.{uA, uM} A ⥤ NondegenerateModuleCat.{uA, uM} A :=
  @NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    (NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor.{uA, uM} e).Additive :=
  @NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor_additive.{uA, uM}

example : {A : Type} → [NonUnitalRing A] → (e : Idempotent A) →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    {N : Type 2} → [AddCommGroup N] → [NonUnitalModule A N] →
    NonUnitalModuleHom A M N →
      NonUnitalModuleHom A (annihilatorQuotientCarrier e M) (annihilatorQuotientCarrier e N) :=
  @NonUnitalModuleHom.annihilatorQuotientMap.{0, 1, 2}

example : {A : Type 1} → [NonUnitalRing A] → (e : Idempotent A) →
    {M : Type} → [AddCommGroup M] → [NonUnitalModule A M] →
    {P : Type 2} → [AddCommGroup P] → [NonUnitalModule A P] →
    (g : NonUnitalModuleHom A M P) → idempotentAnnihilator e M ≤ g.kernelSubmodule →
      NonUnitalModuleHom A (annihilatorQuotientCarrier e M) P :=
  @NonUnitalModuleHom.annihilatorQuotientDesc.{1, 0, 2}

example : {A : Type} → [NonUnitalRing A] → (e : Idempotent A) →
    (NonUnitalModuleCat.annihilatorQuotientFunctor.{0, 1} e).Additive :=
  @NonUnitalModuleCat.annihilatorQuotientFunctor_additive.{0, 1}

example : {A : Type 1} → [NonUnitalRing A] → (e : Idempotent A) →
    NondegenerateModuleCat.{1, 0} A ⥤ NondegenerateModuleCat.{1, 0} A :=
  @NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor.{1, 0}

/-- Instance search on the quotient carrier finds exactly the named quotient structures. -/
example {A : Type uA} [NonUnitalRing A] (e : Idempotent A) (M : Type uM) [AddCommGroup M]
    [NonUnitalModule A M] :
    (inferInstance : NonUnitalModule A (annihilatorQuotientCarrier e M)) =
      (idempotentAnnihilator e M).toIntCompatible.quotientNonUnitalModule := rfl

/-- Over `ℤ` the scalar action on the quotient is still the selected original quotient action,
not the canonical integer action of its additive group. -/
example (e : Idempotent ℤ) (M : Type uM) [AddCommGroup M] [NonUnitalModule ℤ M] :
    (inferInstance : SMul ℤ (annihilatorQuotientCarrier e M)) =
      (annihilatorQuotientModule e M).toSMul := rfl

/-- Over `ℤ` with the zero original action the selected source action is the zero action. -/
example (e : Idempotent ℤ) (M : Type uM) [AddCommGroup M] (m : M) :
    letI : NonUnitalModule ℤ M := NonUnitalModule.zero
    annihilatorQuotientProjection e M ((2 : ℤ) • m) = 0 := rfl

end Langlands.Algebra
