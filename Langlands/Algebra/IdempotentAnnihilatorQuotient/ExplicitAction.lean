import Langlands.Algebra.IntegerNonUnitalSubmodule
import Langlands.Algebra.NondegenerateModuleAdditive

/-!
# The actual quotient by the annihilator of eA

Renard (French version, 9 July 2026), I.3.2, printed p.20 / PDF26.
The ambient arbitrary-ring construction is an internal generalization of the
source's complex idempotented algebra; its nondegenerate restriction is the
source's quotient. No unit action or local-unit hypothesis is imposed here.
-/

set_option autoImplicit false

open CategoryTheory

namespace Langlands.Algebra.IdempotentAnnihilator

universe uA uM uN uP

variable {A : Type uA} [NonUnitalRing A]

/-- The stable annihilator of the whole right ideal `eA`, with the original action. -/
def submodule (e : Idempotent A) (M : Type uM) [AddCommGroup M]
    [NonUnitalModule A M] : NonUnitalSubmodule A M where
  carrier := {m | ∀ a : A, ((e : A) * a) • m = 0}
  zero_mem' := fun a => smul_zero _
  add_mem' := by
    intro m n hm hn a
    rw [smul_add, hm a, hn a, add_zero]
  neg_mem' := by
    intro m hm a
    rw [smul_neg, hm a, neg_zero]
  smul_mem' := by
    intro b m hm a
    rw [← mul_smul, mul_assoc]
    exact hm (a * b)

@[simp] theorem mem_submodule (e : Idempotent A) {M : Type uM}
    [AddCommGroup M] [NonUnitalModule A M] (m : M) :
    m ∈ submodule e M ↔ ∀ a : A, ((e : A) * a) • m = 0 := Iff.rfl

variable (e : Idempotent A)
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]
  {P : Type uP} [AddCommGroup P] [NonUnitalModule A P]

/-- In particular `e` kills every vector of the annihilator, since `e = e*e`. -/
theorem smul_eq_zero_of_mem {m : M} (hm : m ∈ submodule e M) : (e : A) • m = 0 := by
  simpa only [e.property.eq] using hm (e : A)

/-- Among original stable subgroups, this is the largest subgroup killed by `e`. -/
theorem le_submodule_iff (S : NonUnitalSubmodule A M) :
    S ≤ submodule e M ↔ ∀ m ∈ S, (e : A) • m = 0 := by
  constructor
  · intro h m hm
    exact smul_eq_zero_of_mem e (h hm)
  · intro h m hm a
    rw [mul_smul]
    exact h (a • m) (S.smul_mem' a hm)

/-- The actual quotient of the original additive carrier by the stable annihilator. -/
abbrev quotient (e : Idempotent A) (M : Type uM) [AddCommGroup M]
    [NonUnitalModule A M] : Type uM :=
  M ⧸ (submodule e M).toIntCompatible.toSubmodule

/-- The inherited additive group of the actual quotient. -/
abbrev quotientAddCommGroup (e : Idempotent A) (M : Type uM) [AddCommGroup M]
    [NonUnitalModule A M] : AddCommGroup (quotient e M) := inferInstance

/-- Integer compatibility leaves even the actual additive-subgroup quotient carrier unchanged. -/
theorem quotient_eq_addSubgroupQuotient :
    quotient e M = (M ⧸ (submodule e M).toAddSubgroup) := rfl

/-- The inherited group is precisely the additive-subgroup quotient group. -/
theorem quotientAddCommGroup_eq : quotientAddCommGroup e M =
    (inferInstance : AddCommGroup (M ⧸ (submodule e M).toAddSubgroup)) := rfl

/-- The published integer-compatible quotient action, retaining the original action. -/
abbrev quotientNonUnitalModule (e : Idempotent A) (M : Type uM) [AddCommGroup M]
    [NonUnitalModule A M] : NonUnitalModule A (quotient e M) :=
  (submodule e M).toIntCompatible.quotientNonUnitalModule

-- This instance is local to this file. Public interfaces contain this named structure.
attribute [local instance] quotientNonUnitalModule

/-- The complete original additive quotient projection. -/
def projection : NonUnitalModuleHom A M (quotient e M) :=
  (submodule e M).toIntCompatible.mkQNonUnitalModuleHom

@[simp] theorem projection_apply (m : M) :
    projection e m = (Submodule.Quotient.mk m : quotient e M) := rfl

/-- The entire underlying additive map, not only its values on representatives. -/
theorem projection_toAddMonoidHom :
    (projection e (M := M)).toAddMonoidHom =
      (submodule e M).toIntCompatible.toSubmodule.mkQ.toAddMonoidHom := rfl

/-- This formula selects the named quotient action explicitly. -/
theorem quotient_smul_mk (a : A) (m : M) :
    (quotientNonUnitalModule e M).toDistribSMul.smul a (Submodule.Quotient.mk m) =
      (Submodule.Quotient.mk (a • m) : quotient e M) := rfl

/-- Every coset has an actual representative. -/
theorem projection_surjective : Function.Surjective (projection e (M := M)) :=
  Submodule.Quotient.mk_surjective _

@[simp] theorem projection_eq_zero_iff (m : M) :
    projection e m = 0 ↔ m ∈ submodule e M :=
  Submodule.Quotient.mk_eq_zero _

/-- Original intertwiners carry the full eA-annihilator into the full eA-annihilator. -/
theorem map_mem (f : NonUnitalModuleHom A M N) {m : M}
    (hm : m ∈ submodule e M) : f m ∈ submodule e N := by
  intro a
  rw [← f.map_smul, hm a, f.map_zero]

/-- The containment supplied to the published `mapQ` descent. -/
theorem le_comap (f : NonUnitalModuleHom A M N) :
    (submodule e M).toIntCompatible ≤
      (submodule e N).toIntCompatible.comap f.toIntLinearIntertwiner :=
  fun _ hm => map_mem e f hm

/-- The induced original quotient intertwiner, via the published integer-linear `mapQ`. -/
def map (f : NonUnitalModuleHom A M N) :
    NonUnitalModuleHom A (quotient e M) (quotient e N) :=
  (f.toIntLinearIntertwiner.mapQ (submodule e M).toIntCompatible
    (submodule e N).toIntCompatible (le_comap e f)).toNonUnitalModuleHom

@[simp] theorem map_apply_mk (f : NonUnitalModuleHom A M N) (m : M) :
    map e f (Submodule.Quotient.mk m) = Submodule.Quotient.mk (f m) := rfl

/-- The full underlying map is exactly the existing quotient-map construction. -/
theorem map_toAddMonoidHom (f : NonUnitalModuleHom A M N) :
    (map e f).toAddMonoidHom =
      ((submodule e M).toIntCompatible.toSubmodule.mapQ
        (submodule e N).toIntCompatible.toSubmodule
        f.toAddMonoidHom.toIntLinearMap (le_comap e f)).toAddMonoidHom := rfl

/-- Naturality as equality of complete original additive intertwiners. -/
theorem map_comp_projection (f : NonUnitalModuleHom A M N) :
    (map e f).comp (projection e) = (projection e).comp f := rfl

@[simp] theorem map_id : map e (NonUnitalModuleHom.id A M) =
    NonUnitalModuleHom.id A (quotient e M) := by
  apply NonUnitalModuleHom.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H m => rfl

@[simp] theorem map_comp (g : NonUnitalModuleHom A N P) (f : NonUnitalModuleHom A M N) :
    map e (g.comp f) = (map e g).comp (map e f) := by
  apply NonUnitalModuleHom.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H m => rfl

@[simp] theorem map_zero : map e (0 : NonUnitalModuleHom A M N) = 0 := by
  apply NonUnitalModuleHom.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H m => exact (projection e (M := N)).map_zero

@[simp] theorem map_add (f g : NonUnitalModuleHom A M N) :
    map e (f + g) = map e f + map e g := by
  apply NonUnitalModuleHom.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H m => exact (projection e (M := N)).map_add (f m) (g m)

/-- The quotient map is additive on the original Hom groups in independent universes. -/
def mapAddHom : NonUnitalModuleHom A M N →+
    NonUnitalModuleHom A (quotient e M) (quotient e N) where
  toFun := map e
  map_zero' := map_zero e
  map_add' := map_add e

@[simp] theorem mapAddHom_apply (f : NonUnitalModuleHom A M N) :
    mapAddHom e f = map e f := rfl

/-- Descent of any original intertwiner killing the annihilator, using `liftQ`. -/
def desc (f : NonUnitalModuleHom A M N)
    (h : ∀ m ∈ submodule e M, f m = 0) : NonUnitalModuleHom A (quotient e M) N :=
  (f.toIntLinearIntertwiner.liftQ (submodule e M).toIntCompatible h).toNonUnitalModuleHom

@[simp] theorem desc_apply_mk (f : NonUnitalModuleHom A M N)
    (h : ∀ m ∈ submodule e M, f m = 0) (m : M) :
    desc e f h (Submodule.Quotient.mk m) = f m := rfl

/-- The full underlying descent is the existing linear quotient lift. -/
theorem desc_toAddMonoidHom (f : NonUnitalModuleHom A M N)
    (h : ∀ m ∈ submodule e M, f m = 0) :
    (desc e f h).toAddMonoidHom =
      ((submodule e M).toIntCompatible.toSubmodule.liftQ
        f.toAddMonoidHom.toIntLinearMap h).toAddMonoidHom := rfl

@[simp] theorem desc_comp_projection (f : NonUnitalModuleHom A M N)
    (h : ∀ m ∈ submodule e M, f m = 0) :
    (desc e f h).comp (projection e) = f := rfl

/-- Surjectivity of the actual projection gives uniqueness of the entire descent. -/
theorem desc_unique (f : NonUnitalModuleHom A M N)
    (h : ∀ m ∈ submodule e M, f m = 0)
    (g : NonUnitalModuleHom A (quotient e M) N)
    (hg : g.comp (projection e) = f) : g = desc e f h := by
  apply NonUnitalModuleHom.ext
  intro q
  obtain ⟨m, rfl⟩ := projection_surjective e q
  exact congrArg (fun k : NonUnitalModuleHom A M N => k m) hg

/-- The intrinsic universal property, with a unique original intertwiner. -/
theorem existsUnique_desc (f : NonUnitalModuleHom A M N)
    (h : ∀ m ∈ submodule e M, f m = 0) :
    ∃! g : NonUnitalModuleHom A (quotient e M) N, g.comp (projection e) = f :=
  ⟨desc e f h, desc_comp_projection e f h, fun g hg => desc_unique e f h g hg⟩

/-- A fixing idempotent of a representative fixes its class in the quotient. -/
theorem isNondegenerate (h : IsNondegenerate A M) : IsNondegenerate A (quotient e M) := by
  intro q
  obtain ⟨m, rfl⟩ := projection_surjective e q
  obtain ⟨d, hd⟩ := h m
  refine ⟨d, ?_⟩
  rw [← (projection e (M := M)).map_smul, hd]

/-- Negation follows from the additive map on the complete original Hom groups. -/
@[simp] theorem map_neg (f : NonUnitalModuleHom A M N) :
    map e (-f) = -map e f := (mapAddHom e).map_neg f

/-- If every vector is annihilated, every class in the actual quotient is zero. -/
theorem quotient_eq_zero_of_forall_mem (h : ∀ m : M, m ∈ submodule e M)
    (q : quotient e M) : q = 0 := by
  obtain ⟨m, rfl⟩ := projection_surjective e q
  exact (projection_eq_zero_iff e m).2 (h m)

/-- Triviality is proved for the existing quotient carrier. -/
theorem quotient_subsingleton_of_forall_mem (h : ∀ m : M, m ∈ submodule e M) :
    Subsingleton (quotient e M) :=
  ⟨fun q r => (quotient_eq_zero_of_forall_mem e h q).trans
    (quotient_eq_zero_of_forall_mem e h r).symm⟩

/-- A zero idempotent annihilates the whole original module. -/
theorem submodule_eq_univ_of_idempotent_eq_zero (he : (e : A) = 0) :
    (submodule e M : Set M) = Set.univ := by
  ext m
  change (∀ a : A, ((e : A) * a) • m = 0) ↔ True
  exact iff_true_intro (fun a => by rw [he, zero_mul, NonUnitalModule.zero_smul])

/-- With a zero idempotent the actual quotient is trivial, including nonzero modules. -/
theorem quotient_subsingleton_of_idempotent_eq_zero (he : (e : A) = 0) :
    Subsingleton (quotient e M) :=
  quotient_subsingleton_of_forall_mem e (fun m => by
    rw [← SetLike.mem_coe, submodule_eq_univ_of_idempotent_eq_zero e he]
    exact Set.mem_univ m)

/-- A zero original action annihilates every vector for every idempotent. -/
theorem submodule_eq_univ_of_zero_action (h : ∀ (a : A) (m : M), a • m = 0) :
    (submodule e M : Set M) = Set.univ := by
  ext m
  exact iff_true_intro (fun a => h ((e : A) * a) m)

/-- This also covers a specified zero action over a ring with a unit. -/
theorem quotient_subsingleton_of_zero_action (h : ∀ (a : A) (m : M), a • m = 0) :
    Subsingleton (quotient e M) :=
  quotient_subsingleton_of_forall_mem e (fun m a => h ((e : A) * a) m)

/-- A zero carrier has a zero quotient under every specified original action. -/
theorem quotient_subsingleton_of_subsingleton [Subsingleton M] :
    Subsingleton (quotient e M) :=
  quotient_subsingleton_of_zero_action e (fun _ _ => Subsingleton.elim _ _)

/-- The actual quotient object, with the named inherited group and quotient action. -/
def obj (M : NonUnitalModuleCat.{uA, uM} A) : NonUnitalModuleCat.{uA, uM} A :=
  { carrier := quotient e M
    isAddCommGroup := quotientAddCommGroup e M
    isModule := quotientNonUnitalModule e M }

@[simp] theorem obj_carrier (M : NonUnitalModuleCat.{uA, uM} A) :
    (obj e M : Type uM) = quotient e M := rfl

/-- The object's stored action is the selected quotient structure. -/
theorem obj_isModule (M : NonUnitalModuleCat.{uA, uM} A) :
    (obj e M).isModule = quotientNonUnitalModule e M := rfl

/-- The actual endofunctor on all original additive modules. -/
def functor : NonUnitalModuleCat.{uA, uM} A ⥤ NonUnitalModuleCat.{uA, uM} A where
  obj := obj e
  map := map e
  map_id _ := map_id e
  map_comp f g := map_comp e g f

@[simp] theorem functor_obj (M : NonUnitalModuleCat.{uA, uM} A) :
    (functor e).obj M = obj e M := rfl

@[simp] theorem functor_map {M N : NonUnitalModuleCat.{uA, uM} A} (f : M ⟶ N) :
    (functor e).map f = map e f := rfl

instance functor_additive : (functor.{uA, uM} e).Additive where
  map_add := by
    intro M N f g
    exact map_add e f g

/-- The natural quotient projection from the identity functor. -/
def projectionNatTrans : 𝟭 (NonUnitalModuleCat.{uA, uM} A) ⟶ functor e where
  app _ := projection e
  naturality _ _ f := (map_comp_projection e f).symm

@[simp] theorem projectionNatTrans_app (M : NonUnitalModuleCat.{uA, uM} A) :
    (projectionNatTrans e).app M = projection e := rfl

/-- Restriction uses the same actual quotient object and a lifted fixing idempotent. -/
def nondegenerateObj (M : NondegenerateModuleCat.{uA, uM} A) :
    NondegenerateModuleCat.{uA, uM} A :=
  ⟨obj e M.obj, isNondegenerate e M.property⟩

/-- The quotient endofunctor on the source's category of nondegenerate modules. -/
def nondegenerateFunctor :
    NondegenerateModuleCat.{uA, uM} A ⥤ NondegenerateModuleCat.{uA, uM} A where
  obj := nondegenerateObj e
  map f := ObjectProperty.homMk (map e f.hom)
  map_id _ := by
    apply ObjectProperty.hom_ext
    exact map_id e
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact map_comp e g.hom f.hom

@[simp] theorem nondegenerateFunctor_obj (M : NondegenerateModuleCat.{uA, uM} A) :
    ((nondegenerateFunctor e).obj M).obj = obj e M.obj := rfl

@[simp] theorem nondegenerateFunctor_map_hom
    {M N : NondegenerateModuleCat.{uA, uM} A} (f : M ⟶ N) :
    ((nondegenerateFunctor e).map f).hom = map e f.hom := rfl

instance nondegenerateFunctor_additive : (nondegenerateFunctor.{uA, uM} e).Additive where
  map_add := by
    intro M N f g
    apply ObjectProperty.hom_ext
    exact map_add e f.hom g.hom

/-- The source's quotient projections, as an actual natural transformation. -/
def nondegenerateProjectionNatTrans :
    𝟭 (NondegenerateModuleCat.{uA, uM} A) ⟶ nondegenerateFunctor e where
  app _ := ObjectProperty.homMk (projection e)
  naturality _ _ f := by
    apply ObjectProperty.hom_ext
    exact (map_comp_projection e f.hom).symm

@[simp] theorem nondegenerateProjectionNatTrans_app_hom
    (M : NondegenerateModuleCat.{uA, uM} A) :
    ((nondegenerateProjectionNatTrans e).app M).hom = projection e := rfl

/-- The ambient and restricted functors agree through the published inclusion. -/
theorem nondegenerateFunctor_comp_inclusion :
    nondegenerateFunctor.{uA, uM} e ⋙ nondegenerateInclusion A =
      nondegenerateInclusion A ⋙ functor e := rfl

/-- After inclusion, every restricted projection is the ambient projection itself. -/
theorem nondegenerateProjection_app_inclusion (M : NondegenerateModuleCat.{uA, uM} A) :
    (nondegenerateInclusion A).map ((nondegenerateProjectionNatTrans e).app M) =
      (projectionNatTrans e).app ((nondegenerateInclusion A).obj M) := rfl

/-! Complete, unapplied declaration checks and checks with competing actions. -/

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    (M : Type uM) → [AddCommGroup M] → [NonUnitalModule A M] → NonUnitalSubmodule A M :=
  @submodule.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    (M : Type uM) → [AddCommGroup M] → [NonUnitalModule A M] → Type uM :=
  @quotient.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    NonUnitalModuleHom A M (quotient e M) := @projection.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule A N] →
    NonUnitalModuleHom A M N → NonUnitalModuleHom A (quotient e M) (quotient e N) :=
  @map.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule A N] →
    NonUnitalModuleHom A M N →+ NonUnitalModuleHom A (quotient e M) (quotient e N) :=
  @mapAddHom.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    {N : Type uN} → [AddCommGroup N] → [NonUnitalModule A N] →
    (f : NonUnitalModuleHom A M N) → (∀ m ∈ submodule e M, f m = 0) →
    NonUnitalModuleHom A (quotient e M) N := @desc.{uA, uM, uN}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    NonUnitalModuleCat.{uA, uM} A ⥤ NonUnitalModuleCat.{uA, uM} A := @functor.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    𝟭 (NonUnitalModuleCat.{uA, uM} A) ⟶ functor e := @projectionNatTrans.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    NondegenerateModuleCat.{uA, uM} A ⥤ NondegenerateModuleCat.{uA, uM} A :=
  @nondegenerateFunctor.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (e : Idempotent A) →
    𝟭 (NondegenerateModuleCat.{uA, uM} A) ⟶ nondegenerateFunctor e :=
  @nondegenerateProjectionNatTrans.{uA, uM}

-- A ring and two carrier universes may all differ, in either size direction.
example : {A : Type} → [NonUnitalRing A] → (e : Idempotent A) →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    {N : Type 2} → [AddCommGroup N] → [NonUnitalModule A N] →
    NonUnitalModuleHom A M N → NonUnitalModuleHom A (quotient e M) (quotient e N) :=
  @map.{0, 1, 2}

example : {A : Type 2} → [NonUnitalRing A] → (e : Idempotent A) →
    {M : Type 1} → [AddCommGroup M] → [NonUnitalModule A M] →
    {N : Type} → [AddCommGroup N] → [NonUnitalModule A N] →
    (f : NonUnitalModuleHom A M N) → (∀ m ∈ submodule e M, f m = 0) →
    NonUnitalModuleHom A (quotient e M) N := @desc.{2, 1, 0}

-- Explicit structure arguments prevent another quotient action from being selected.
example [_hQ : NonUnitalModule A (quotient e M)] :
    @NonUnitalModuleHom A M (quotient e M) _ _ _
      (inferInstance : NonUnitalModule A M) (quotientNonUnitalModule e M) := projection e

example [_hQM : NonUnitalModule A (quotient e M)]
    [_hQN : NonUnitalModule A (quotient e N)] (f : NonUnitalModuleHom A M N) :
    @NonUnitalModuleHom A (quotient e M) (quotient e N) _ _ _
      (quotientNonUnitalModule e M) (quotientNonUnitalModule e N) := map e f

example [_hQ : NonUnitalModule A (quotient e M)] (f : NonUnitalModuleHom A M N)
    (h : ∀ m ∈ submodule e M, f m = 0) :
    @NonUnitalModuleHom A (quotient e M) N _ _ _
      (quotientNonUnitalModule e M) (inferInstance : NonUnitalModule A N) := desc e f h

example [_hQ : NonUnitalModule A (quotient e M)]
    (a : A) (m : M) :
    (quotientNonUnitalModule e M).toDistribSMul.smul a (Submodule.Quotient.mk m) =
      (Submodule.Quotient.mk (a • m) : quotient e M) := quotient_smul_mk e a m

example : Subsingleton (quotient (⟨0, IsIdempotentElem.zero⟩ : Idempotent A) M) :=
  quotient_subsingleton_of_idempotent_eq_zero _ rfl

-- Even over the integers, the specified zero original action is retained.
example (d : Idempotent ℤ) :
    let _ := (NonUnitalModule.zero : NonUnitalModule ℤ ℤ)
    (submodule d ℤ : Set ℤ) = Set.univ := by
  let _ := (NonUnitalModule.zero : NonUnitalModule ℤ ℤ)
  exact submodule_eq_univ_of_zero_action d (fun _ _ => rfl)

example (d : Idempotent ℤ) :
    let _ := (NonUnitalModule.zero : NonUnitalModule ℤ ℤ)
    Subsingleton (quotient d ℤ) := by
  let _ := (NonUnitalModule.zero : NonUnitalModule ℤ ℤ)
  exact quotient_subsingleton_of_zero_action d (fun _ _ => rfl)

example : letI := (NonUnitalModule.zero : NonUnitalModule A PUnit)
    Subsingleton (quotient e PUnit) := by
  let _ := (NonUnitalModule.zero : NonUnitalModule A PUnit)
  exact quotient_subsingleton_of_subsingleton e

end Langlands.Algebra.IdempotentAnnihilator
