import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.Transfer.SubquotientProof

/-!
# Actual subquotients in the smooth representation category

The actions and maps are Mathlib's actual restrictions and module quotients.
Smoothness is supplied by the accepted injective/surjective transfer theorem.
-/

open CategoryTheory

namespace Langlands.SmoothRep

universe uR uG uV

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G]
  [TopologicalSpace G]

variable (A : SmoothRep.{uR, uG, uV} R G)

/-- The invariant-submodule stability certificate in the form required by `Rep`. -/
theorem stable (S : Subrepresentation A.representation) (g : G) :
    S.toSubmodule ≤ S.toSubmodule.comap (A.representation g) :=
  fun _ hv => S.apply_mem_toSubmodule g hv

/-- The smooth representation on an actual invariant submodule. -/
def subrepresentation (S : Subrepresentation A.representation) : SmoothRep R G :=
  ⟨A.obj.subrepresentation S.toSubmodule (stable A S),
    Langlands.isSmooth_of_injective
      (A.obj.subtype S.toSubmodule (stable A S)).hom
      (Submodule.injective_subtype _) A.isSmooth⟩

/-- The canonical inclusion of a smooth subrepresentation. -/
def subtype (S : Subrepresentation A.representation) : subrepresentation A S ⟶ A :=
  ObjectProperty.homMk (A.obj.subtype S.toSubmodule (stable A S))

theorem subtype_injective (S : Subrepresentation A.representation) :
    Function.Injective (hom (subtype A S)) :=
  Submodule.injective_subtype _

/-- The smooth representation on the actual quotient module by an invariant
submodule. No choice of an abstract quotient object is made. -/
def quotient (S : Subrepresentation A.representation) : SmoothRep R G :=
  ⟨A.obj.quotient S.toSubmodule (stable A S),
    Langlands.isSmooth_of_surjective
      (A.obj.mkQ S.toSubmodule (stable A S)).hom
      (Submodule.mkQ_surjective _) A.isSmooth⟩

/-- The canonical equivariant quotient map. -/
def mkQ (S : Subrepresentation A.representation) : A ⟶ quotient A S :=
  ObjectProperty.homMk (A.obj.mkQ S.toSubmodule (stable A S))

theorem mkQ_surjective (S : Subrepresentation A.representation) :
    Function.Surjective (hom (mkQ A S)) :=
  Submodule.mkQ_surjective _

/-- A subquotient is formed by taking an invariant submodule and then quotienting
it by one of its invariant submodules. -/
def subquotient (S : Subrepresentation A.representation)
    (T : Subrepresentation (subrepresentation A S).representation) : SmoothRep R G :=
  quotient (subrepresentation A S) T

variable {A} {B : SmoothRep.{uR, uG, uV} R G}

/-- The actual invariant kernel representation of an intertwiner. -/
def kernel (f : A ⟶ B) : SmoothRep R G :=
  subrepresentation A (hom f).ker

/-- Its canonical injective intertwiner into the source. -/
def kernelι (f : A ⟶ B) : kernel f ⟶ A :=
  subtype A (hom f).ker

/-- The actual invariant image representation of an intertwiner. -/
def image (f : A ⟶ B) : SmoothRep R G :=
  subrepresentation B (hom f).range

/-- Its canonical inclusion into the target. -/
def imageι (f : A ⟶ B) : image f ⟶ B :=
  subtype B (hom f).range

/-- The actual smooth quotient of the target by the invariant image. -/
def cokernel (f : A ⟶ B) : SmoothRep R G :=
  quotient B (hom f).range

/-- Its canonical quotient map. -/
def cokernelπ (f : A ⟶ B) : B ⟶ cokernel f :=
  mkQ B (hom f).range

/-- Being a quotient means there is an actual surjective intertwiner. -/
def IsQuotient (B A : SmoothRep.{uR, uG, uV} R G) : Prop :=
  ∃ f : A ⟶ B, Function.Surjective (hom f)

/-- Being a subrepresentation up to isomorphism means there is an actual
injective intertwiner into the ambient representation. -/
def IsSubrepresentation (B A : SmoothRep.{uR, uG, uV} R G) : Prop :=
  ∃ f : B ⟶ A, Function.Injective (hom f)

/-- The subquotient relation retains an actual submodule and actual quotient,
then allows an isomorphism to the representation in question. -/
def IsSubquotient (B A : SmoothRep.{uR, uG, uV} R G) : Prop :=
  ∃ (S : Subrepresentation A.representation)
    (T : Subrepresentation (subrepresentation A S).representation),
    Nonempty (B ≅ subquotient A S T)

theorem subrepresentation_isSubrepresentation
    (S : Subrepresentation A.representation) :
    IsSubrepresentation (subrepresentation A S) A :=
  ⟨subtype A S, subtype_injective A S⟩

theorem quotient_isQuotient (S : Subrepresentation A.representation) :
    IsQuotient (quotient A S) A :=
  ⟨mkQ A S, mkQ_surjective A S⟩

end Langlands.SmoothRep
