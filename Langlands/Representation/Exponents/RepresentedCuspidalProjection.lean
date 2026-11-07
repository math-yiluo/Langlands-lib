import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport
import Langlands.Representation.Exponents.JacquetNontrivialityTransfer
import Langlands.Representation.Category.Abelian
import Langlands.Representation.Category.CoproductSize

/-! # The supercuspidal part of represented cuspidal/remainder splittings

Represented supercuspidality passes to subrepresentations, quotients and subquotients.
Every morphism between a supercuspidal representation and a representation without
nontrivial supercuspidal subquotients vanishes, in both directions. Consequently the
supercuspidal summands of chosen cuspidal/remainder splittings form an additive functor
that preserves monomorphisms and epimorphisms. The splittings are supplied: their
existence is not proved here.
-/

noncomputable section

universe u v

open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance cuspidalProjectionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- No nontrivial actual subquotient is supercuspidal: the condition imposed on the
remainder summand by `HasCuspidalRemainderSplitting`. -/
def HasNoSupercuspidalSubquotient (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) : Prop :=
  ∀ D : SmoothRep.{0, u, v} ℂ (rationalPoints G),
    Nontrivial D → SmoothRep.IsSubquotient D A → ¬ IsSupercuspidal D

namespace IsSupercuspidal

variable {A B : SmoothRep.{0, u, v} ℂ (rationalPoints G)}

/-- Supercuspidality passes to the target of a surjective morphism. -/
theorem of_surjective (f : A ⟶ B) (hf : Function.Surjective (SmoothRep.hom f))
    (hA : IsSupercuspidal A) : IsSupercuspidal B := by
  intro P M U p l r hp hl hr hmul hproper
  by_contra h
  rw [not_subsingleton_iff_nontrivial] at h
  have := nontrivial_jacquet_of_surjective p l r hp hl hr hmul f hf
  exact not_nontrivial_iff_subsingleton.mpr (hA P M U p l r hp hl hr hmul hproper) this

/-- Supercuspidality passes to quotients. -/
theorem of_epi (f : A ⟶ B) [Epi f] (hA : IsSupercuspidal A) : IsSupercuspidal B :=
  of_surjective f ((SmoothRep.epi_iff_surjective f).mp inferInstance) hA

/-- Supercuspidality is invariant under isomorphism. -/
theorem of_iso (e : A ≅ B) (hA : IsSupercuspidal A) : IsSupercuspidal B :=
  of_epi e.hom hA

end IsSupercuspidal

/-- An image that is supercuspidal and a subquotient of a representation without
supercuspidal subquotients is zero. -/
private theorem isZero_of_isSupercuspidal_of_isSubquotient
    {D B : SmoothRep.{0, u, v} ℂ (rationalPoints G)} (hB : HasNoSupercuspidalSubquotient B)
    (hD : IsSupercuspidal D) (hDB : SmoothRep.IsSubquotient D B) : IsZero D := by
  rw [SmoothRep.isZero_iff_subsingleton]
  by_contra h
  rw [not_subsingleton_iff_nontrivial] at h
  exact hB D h hDB hD

/-- Every morphism from a supercuspidal representation to a representation without
nontrivial supercuspidal subquotients is zero: its image is both. -/
theorem hom_eq_zero_of_isSupercuspidal_of_hasNoSupercuspidalSubquotient
    {C B : SmoothRep.{0, u, v} ℂ (rationalPoints G)} (hC : IsSupercuspidal C)
    (hB : HasNoSupercuspidalSubquotient B) (f : C ⟶ B) : f = 0 := by
  have hI : IsSupercuspidal (image f) := hC.of_epi (factorThruImage f)
  have hsub : SmoothRep.IsSubquotient (image f) B :=
    SmoothRep.isSubquotient_iff_exists.mpr ⟨image f, image.ι f, 𝟙 _,
      (SmoothRep.mono_iff_injective _).mp inferInstance,
      (SmoothRep.epi_iff_surjective _).mp inferInstance⟩
  have hzero := isZero_of_isSupercuspidal_of_isSubquotient hB hI hsub
  calc f = factorThruImage f ≫ image.ι f := (image.fac f).symm
    _ = 0 := by rw [hzero.eq_of_src (image.ι f) 0, comp_zero]

/-- Chosen data of a cuspidal/remainder splitting: the summand `true` is supercuspidal,
the summand `false` has no nontrivial supercuspidal subquotient, and the inclusions
form an actual coproduct. -/
structure CuspidalRemainderSplitting (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) where
  /-- The two summands. -/
  summand : Bool → SmoothRep.{0, u, v} ℂ (rationalPoints G)
  /-- The coproduct inclusions. -/
  inj : ∀ b, summand b ⟶ A
  isSupercuspidal_true : IsSupercuspidal (summand true)
  hasNoSupercuspidalSubquotient_false : HasNoSupercuspidalSubquotient (summand false)
  /-- The inclusions form a coproduct. -/
  isColimit : IsColimit (Cofan.mk A inj)

/-- A splitting chosen from the existence statement. -/
def HasCuspidalRemainderSplitting.splitting {A : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
    (h : HasCuspidalRemainderSplitting A) : CuspidalRemainderSplitting A where
  summand := h.choose
  inj := h.choose_spec.choose
  isSupercuspidal_true := h.choose_spec.choose_spec.1
  hasNoSupercuspidalSubquotient_false := h.choose_spec.choose_spec.2.1
  isColimit := h.choose_spec.choose_spec.2.2.some

namespace CuspidalRemainderSplitting

variable {A B : SmoothRep.{0, u, v} ℂ (rationalPoints G)}

/-- Chosen data witness the existence statement. -/
theorem hasCuspidalRemainderSplitting (s : CuspidalRemainderSplitting A) :
    HasCuspidalRemainderSplitting A :=
  ⟨s.summand, s.inj, s.isSupercuspidal_true, s.hasNoSupercuspidalSubquotient_false,
    ⟨s.isColimit⟩⟩

variable (s : CuspidalRemainderSplitting A)

/-- The projection onto the supercuspidal summand. -/
def cuspidalProjection : A ⟶ s.summand true :=
  Cofan.IsColimit.desc s.isColimit fun b => match b with
    | true => 𝟙 _
    | false => 0

/-- The projection onto the remainder summand. -/
def remainderProjection : A ⟶ s.summand false :=
  Cofan.IsColimit.desc s.isColimit fun b => match b with
    | true => 0
    | false => 𝟙 _

@[reassoc (attr := simp)]
theorem inj_true_cuspidalProjection : s.inj true ≫ s.cuspidalProjection = 𝟙 _ :=
  Cofan.IsColimit.fac s.isColimit _ true

@[reassoc (attr := simp)]
theorem inj_false_cuspidalProjection : s.inj false ≫ s.cuspidalProjection = 0 :=
  Cofan.IsColimit.fac s.isColimit _ false

@[reassoc (attr := simp)]
theorem inj_true_remainderProjection : s.inj true ≫ s.remainderProjection = 0 :=
  Cofan.IsColimit.fac s.isColimit _ true

@[reassoc (attr := simp)]
theorem inj_false_remainderProjection : s.inj false ≫ s.remainderProjection = 𝟙 _ :=
  Cofan.IsColimit.fac s.isColimit _ false

/-- The two idempotents of the splitting add up to the identity. -/
theorem projection_add :
    s.cuspidalProjection ≫ s.inj true + s.remainderProjection ≫ s.inj false = 𝟙 A := by
  apply Cofan.IsColimit.hom_ext s.isColimit
  intro b
  cases b <;> simp [Preadditive.comp_add]

instance : IsSplitMono (s.inj true) :=
  IsSplitMono.mk' ⟨s.cuspidalProjection, s.inj_true_cuspidalProjection⟩

instance : IsSplitEpi s.cuspidalProjection :=
  IsSplitEpi.mk' ⟨s.inj true, s.inj_true_cuspidalProjection⟩

instance : IsSplitEpi s.remainderProjection :=
  IsSplitEpi.mk' ⟨s.inj false, s.inj_false_remainderProjection⟩

/-- The supercuspidal summand is a quotient of the split representation. -/
theorem isSupercuspidal_remainder_of_isSupercuspidal (hA : IsSupercuspidal A) :
    IsSupercuspidal (s.summand false) :=
  hA.of_epi s.remainderProjection

/-- For a supercuspidal representation the remainder summand is zero. -/
theorem isZero_remainder_of_isSupercuspidal (hA : IsSupercuspidal A) :
    IsZero (s.summand false) :=
  isZero_of_isSupercuspidal_of_isSubquotient s.hasNoSupercuspidalSubquotient_false
    (s.isSupercuspidal_remainder_of_isSupercuspidal hA)
    (SmoothRep.isSubquotient_iff_exists.mpr ⟨s.summand false, 𝟙 _, 𝟙 _,
      (SmoothRep.mono_iff_injective _).mp inferInstance,
      (SmoothRep.epi_iff_surjective _).mp inferInstance⟩)

/-- A supercuspidal representation whose supercuspidal summand is zero is zero. -/
theorem isZero_of_isSupercuspidal (hA : IsSupercuspidal A)
    (h0 : IsZero (s.summand true)) : IsZero A := by
  rw [IsZero.iff_id_eq_zero, ← s.projection_add,
    h0.eq_of_tgt s.cuspidalProjection 0,
    (s.isZero_remainder_of_isSupercuspidal hA).eq_of_tgt s.remainderProjection 0]
  simp

variable {s} (t : CuspidalRemainderSplitting B)

/-- The supercuspidal-to-supercuspidal component of a morphism of split
representations. -/
def cuspidalMap (f : A ⟶ B) : s.summand true ⟶ t.summand true :=
  s.inj true ≫ f ≫ t.cuspidalProjection

variable (s) in
/-- The supercuspidal-to-remainder component of every morphism vanishes. -/
theorem inj_true_comp_remainderProjection (f : A ⟶ B) :
    s.inj true ≫ f ≫ t.remainderProjection = 0 :=
  hom_eq_zero_of_isSupercuspidal_of_hasNoSupercuspidalSubquotient s.isSupercuspidal_true
    t.hasNoSupercuspidalSubquotient_false _

/-- The supercuspidal inclusions are natural. -/
@[reassoc]
theorem cuspidalMap_inj (f : A ⟶ B) :
    cuspidalMap t f ≫ t.inj true = s.inj true ≫ f := by
  calc cuspidalMap t f ≫ t.inj true
      = s.inj true ≫ f ≫
          (t.cuspidalProjection ≫ t.inj true + t.remainderProjection ≫ t.inj false) := by
        rw [Preadditive.comp_add, Preadditive.comp_add,
          reassoc_of% (inj_true_comp_remainderProjection s t f), zero_comp, add_zero]
        simp only [cuspidalMap, Category.assoc]
    _ = s.inj true ≫ f := by rw [t.projection_add, Category.comp_id]

end CuspidalRemainderSplitting

open CuspidalRemainderSplitting

variable (hs : ∀ A : SmoothRep.{0, u, v} ℂ (rationalPoints G), HasCuspidalRemainderSplitting A)

/-- The supercuspidal-part functor determined by chosen cuspidal/remainder splittings of
all smooth representations. -/
def cuspidalPartFunctor :
    SmoothRep.{0, u, v} ℂ (rationalPoints G) ⥤ SmoothRep.{0, u, v} ℂ (rationalPoints G) where
  obj A := (hs A).splitting.summand true
  map {A B} f := cuspidalMap (s := (hs A).splitting) (hs B).splitting f
  map_id A := by simp [cuspidalMap]
  map_comp {A B C} f g := by
    change _ = cuspidalMap (s := (hs A).splitting) (hs B).splitting f ≫
      ((hs B).splitting.inj true ≫ g ≫ (hs C).splitting.cuspidalProjection)
    rw [cuspidalMap_inj_assoc]
    simp only [cuspidalMap, Category.assoc]

/-- The objects of the functor are the chosen supercuspidal summands. -/
theorem cuspidalPartFunctor_obj (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    (cuspidalPartFunctor hs).obj A = (hs A).splitting.summand true := rfl

/-- The functor's values are supercuspidal. -/
theorem isSupercuspidal_cuspidalPartFunctor_obj
    (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    IsSupercuspidal ((cuspidalPartFunctor hs).obj A) :=
  (hs A).splitting.isSupercuspidal_true

/-- The chosen supercuspidal inclusions form a natural transformation to the identity. -/
def cuspidalPartι : cuspidalPartFunctor hs ⟶ 𝟭 _ where
  app A := (hs A).splitting.inj true
  naturality {A B} f := cuspidalMap_inj (s := (hs A).splitting) (hs B).splitting f

instance (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) : Mono ((cuspidalPartι hs).app A) :=
  inferInstanceAs (Mono ((hs A).splitting.inj true))

instance : (cuspidalPartFunctor hs).Additive where
  map_add {A B f g} := by
    change cuspidalMap (s := (hs A).splitting) (hs B).splitting (f + g) =
      cuspidalMap (s := (hs A).splitting) (hs B).splitting f +
        cuspidalMap (s := (hs A).splitting) (hs B).splitting g
    simp only [cuspidalMap, Preadditive.add_comp, Preadditive.comp_add]

instance : (cuspidalPartFunctor hs).PreservesMonomorphisms where
  preserves {A B} f _ := by
    have : Mono ((cuspidalPartFunctor hs).map f ≫ (cuspidalPartι hs).app B) := by
      rw [(cuspidalPartι hs).naturality f, Functor.id_map]
      exact mono_comp _ _
    exact mono_of_mono _ ((cuspidalPartι hs).app B)

/-- A supercuspidal representation with zero supercuspidal part is zero. -/
theorem isZero_of_isSupercuspidal_of_isZero_cuspidalPartFunctor_obj
    {A : SmoothRep.{0, u, v} ℂ (rationalPoints G)} (hA : IsSupercuspidal A)
    (h0 : IsZero ((cuspidalPartFunctor hs).obj A)) : IsZero A :=
  (hs A).splitting.isZero_of_isSupercuspidal hA h0

section LocalField

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]

namespace IsSupercuspidal

variable {A B : SmoothRep.{0, u, v} ℂ (rationalPoints G)}

/-- Supercuspidality passes to the source of an injective morphism. -/
theorem of_injective (f : A ⟶ B) (hf : Function.Injective (SmoothRep.hom f))
    (hB : IsSupercuspidal B) : IsSupercuspidal A := by
  intro P M U p l r hp hl hr hmul hproper
  by_contra h
  rw [not_subsingleton_iff_nontrivial] at h
  have := nontrivial_jacquet_of_injective p l r hp hl hr hmul f hf
  exact not_nontrivial_iff_subsingleton.mpr (hB P M U p l r hp hl hr hmul hproper) this

/-- Supercuspidality passes to subobjects. -/
theorem of_mono (f : A ⟶ B) [Mono f] (hB : IsSupercuspidal B) : IsSupercuspidal A :=
  of_injective f ((SmoothRep.mono_iff_injective f).mp inferInstance) hB

/-- Supercuspidality passes to actual subquotients. -/
theorem of_isSubquotient (h : SmoothRep.IsSubquotient B A) (hA : IsSupercuspidal A) :
    IsSupercuspidal B := by
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp h
  exact of_surjective q hq (of_injective i hi hA)

end IsSupercuspidal

/-- Every morphism from a representation without nontrivial supercuspidal subquotients
to a supercuspidal representation is zero: its image is both. -/
theorem hom_eq_zero_of_hasNoSupercuspidalSubquotient_of_isSupercuspidal
    {B C : SmoothRep.{0, u, v} ℂ (rationalPoints G)} (hB : HasNoSupercuspidalSubquotient B)
    (hC : IsSupercuspidal C) (f : B ⟶ C) : f = 0 := by
  have hI : IsSupercuspidal (image f) := hC.of_mono (image.ι f)
  have hsub : SmoothRep.IsSubquotient (image f) B :=
    SmoothRep.isSubquotient_iff_exists.mpr ⟨B, 𝟙 B, factorThruImage f,
      (SmoothRep.mono_iff_injective _).mp inferInstance,
      (SmoothRep.epi_iff_surjective _).mp inferInstance⟩
  have hzero := isZero_of_isSupercuspidal_of_isSubquotient hB hI hsub
  calc f = factorThruImage f ≫ image.ι f := (image.fac f).symm
    _ = 0 := by rw [hzero.eq_of_src (image.ι f) 0, comp_zero]

namespace CuspidalRemainderSplitting

variable {A B : SmoothRep.{0, u, v} ℂ (rationalPoints G)} (s : CuspidalRemainderSplitting A)
  (t : CuspidalRemainderSplitting B)

/-- The remainder-to-supercuspidal component of every morphism vanishes. -/
theorem inj_false_comp_cuspidalProjection (f : A ⟶ B) :
    s.inj false ≫ f ≫ t.cuspidalProjection = 0 :=
  hom_eq_zero_of_hasNoSupercuspidalSubquotient_of_isSupercuspidal
    s.hasNoSupercuspidalSubquotient_false t.isSupercuspidal_true _

variable {s} in
/-- The supercuspidal projections are natural. -/
@[reassoc]
theorem cuspidalProjection_cuspidalMap (f : A ⟶ B) :
    s.cuspidalProjection ≫ cuspidalMap t f = f ≫ t.cuspidalProjection := by
  calc s.cuspidalProjection ≫ cuspidalMap t f
      = (s.cuspidalProjection ≫ s.inj true + s.remainderProjection ≫ s.inj false) ≫
          f ≫ t.cuspidalProjection := by
        rw [Preadditive.add_comp, Category.assoc, Category.assoc,
          inj_false_comp_cuspidalProjection s t f, comp_zero, add_zero, cuspidalMap]
    _ = f ≫ t.cuspidalProjection := by rw [s.projection_add, Category.id_comp]

end CuspidalRemainderSplitting

variable (hs : ∀ A : SmoothRep.{0, u, v} ℂ (rationalPoints G), HasCuspidalRemainderSplitting A)

/-- The chosen supercuspidal projections form a natural transformation from the
identity. -/
def cuspidalPartπ : 𝟭 _ ⟶ cuspidalPartFunctor hs where
  app A := (hs A).splitting.cuspidalProjection
  naturality {A B} f :=
    (cuspidalProjection_cuspidalMap (s := (hs A).splitting) (hs B).splitting f).symm

/-- The functor's value is a retract of the original representation. -/
@[reassoc (attr := simp)]
theorem cuspidalPartι_app_cuspidalPartπ_app (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    (cuspidalPartι hs).app A ≫ (cuspidalPartπ hs).app A = 𝟙 _ :=
  (hs A).splitting.inj_true_cuspidalProjection

instance (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)) : Epi ((cuspidalPartπ hs).app A) :=
  inferInstanceAs (Epi (hs A).splitting.cuspidalProjection)

instance : (cuspidalPartFunctor hs).PreservesEpimorphisms where
  preserves {A B} f _ := by
    have : Epi ((cuspidalPartπ hs).app A ≫ (cuspidalPartFunctor hs).map f) := by
      rw [← (cuspidalPartπ hs).naturality f, Functor.id_map]
      exact epi_comp _ _
    exact epi_of_epi ((cuspidalPartπ hs).app A) _

end LocalField

end Langlands.Aubert.General.RepresentedParabolic
