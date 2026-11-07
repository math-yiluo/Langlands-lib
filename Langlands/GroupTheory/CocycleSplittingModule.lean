import Langlands.GroupTheory.CocycleCohomology
import Langlands.Cohomology.Tate.ShiftDefinitions

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.NormalizedTwoCocycle

set_option backward.isDefEq.respectTransparency false

attribute [-instance] ULift.module

namespace SplittingModule

variable (G : Type u) [Group G] [Fintype G]

abbrev Scalars := CoefficientScalars.{u}

/-- Sum of the coordinates of the integral regular module. -/
def coordinateSum : (G → Scalars.{u}) →ₗ[Scalars.{u}] Scalars.{u} :=
  ∑ g : G, LinearMap.proj g

omit [Group G] in
lemma coordinateSum_apply (f : G → Scalars.{u}) :
    coordinateSum G f = ∑ g : G, f g := by
  simp [coordinateSum]

/-- The regular module, written as functions with right translation. -/
def regular : Rep.{u} Scalars.{u} G :=
  Rep.of (X := G → Scalars.{u})
    { toFun g :=
        { toFun f x := f (x * g)
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      map_one' := by ext f x; simp
      map_mul' g h := by ext f x; simp [mul_assoc] }

omit [Fintype G] in
@[simp] lemma regular_apply (g : G) (f : G → Scalars.{u}) (x : G) :
    (regular G).ρ g f x = f (x * g) := rfl

lemma coordinateSum_regular (g : G) (f : G → Scalars.{u}) :
    coordinateSum G ((regular G).ρ g f) = coordinateSum G f := by
  rw [coordinateSum_apply, coordinateSum_apply]
  exact Equiv.sum_comp (Equiv.mulRight g) f

/-- The concrete augmentation ideal of the integral regular module. -/
abbrev Ideal := LinearMap.ker (coordinateSum G)

/-- Translation restricted to the augmentation ideal. -/
def idealAction (g : G) : Ideal G →ₗ[Scalars.{u}] Ideal G where
  toFun f := ⟨(regular G).ρ g f.val, by
    change coordinateSum G ((regular G).ρ g f.val) = 0
    rw [coordinateSum_regular]
    exact f.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- The augmentation ideal with its actual group action. -/
def ideal : Rep.{u} Scalars.{u} G :=
  Rep.of (X := Ideal G)
    { toFun := idealAction G
      map_one' := LinearMap.ext fun f => Subtype.ext (funext fun x => by
        change (f : G → Scalars.{u}) (x * 1) = f.val x
        rw [mul_one])
      map_mul' g h := by
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        funext x
        change (f : G → Scalars.{u}) (x * (g * h)) = f.val ((x * g) * h)
        rw [mul_assoc] }

@[simp] lemma ideal_apply (g : G) (f : Ideal G) (x : G) :
    ((ideal G).ρ g f).val x = f.val (x * g) := rfl

/-- Inclusion of the augmentation ideal into the regular module. -/
def idealInclusion : ideal G ⟶ regular G :=
  Rep.ofHom ⟨(coordinateSum G).ker.subtype, fun _ => rfl⟩

/-- Augmentation to the trivial integral representation. -/
def augmentation : regular G ⟶ Tate.integralTrivial G :=
  Rep.ofHom ⟨coordinateSum G, fun g => by
    apply LinearMap.ext
    intro f
    exact coordinateSum_regular G g f⟩

/-- A coordinate vector of the integral regular module. -/
def delta (g : G) : G → Scalars.{u} := by
  classical
  exact Pi.single g 1

omit [Group G] in
lemma coordinateSum_delta (g : G) : coordinateSum G (delta G g) = 1 := by
  classical
  simp [coordinateSum_apply, delta, Pi.single_apply]

/-- The standard augmentation exact sequence with concrete coordinate carriers. -/
def idealSequence : ShortComplex (Rep.{u} Scalars.{u} G) :=
  ShortComplex.mk (idealInclusion G) (augmentation G) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro f
    change coordinateSum G f.val = 0
    exact f.property)

lemma idealSequence_shortExact : (idealSequence G).ShortExact where
  exact := (forget₂ (Rep.{u} Scalars.{u} G) (ModuleCat Scalars.{u})).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun f hf =>
      ⟨(⟨f, hf⟩ : Ideal G), rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 fun _ _ h => Subtype.ext h
  epi_g := (Rep.epi_iff_surjective _).2 fun r => by
    change Scalars.{u} at r
    refine ⟨r • delta G 1, ?_⟩
    change coordinateSum G (r • delta G 1) = r
    rw [map_smul, coordinateSum_delta, smul_eq_mul, mul_one]

/-- The regular module is the already constructed coinduced integral module. -/
def regularIsoCoinduced : regular G ≅ Tate.coinduced (Tate.integralTrivial G) :=
  { hom := Rep.ofHom ⟨(Tate.coinducedFunctions (Tate.integralTrivial G)).toLinearMap,
      fun _ => rfl⟩
    inv := Rep.ofHom ⟨(Tate.coinducedFunctions (Tate.integralTrivial G)).symm.toLinearMap,
      fun _ => rfl⟩
    hom_inv_id := by ext f; rfl
    inv_hom_id := by ext f; rfl }

lemma regular_tate_isZero (n : ℤ) : IsZero (tateCohomology (regular G) n) :=
  (Tate.coinduced_tate_isZero (Tate.integralTrivial G) n).of_iso
    ((tateCohomologyFunctor n).mapIso (regularIsoCoinduced G))

end SplittingModule

end Langlands.NormalizedTwoCocycle
