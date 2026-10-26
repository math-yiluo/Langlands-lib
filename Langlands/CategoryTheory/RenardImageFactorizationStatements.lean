import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Renard A.VI.2(1, 4–5): balancedness, images, coimages and factorization

Statements of Renard 2026, Appendix A.VI.2(1), (4) and (5), printed page 262 /
PDF page 268, with the subobject and quotient orders of A.I.2, printed page 248 /
PDF page 254. The image is the actual kernel of the cokernel and the coimage is
the actual cokernel of the kernel.
-/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits

universe u v

section UniversalProperties

variable {C : Type u} [Category.{v} C]

/-- The factorization `e ≫ m` of `f` is least among factorizations of `f` through
a monomorphism: every factorization `e' ≫ m' = f` with `m'` mono receives a unique
map `t` with `t ≫ m' = m` and `e ≫ t = e'`. This is Renard's image as the least
subobject through which `f` factors. -/
def ImageUniversalProperty {X Y I : C} (f : X ⟶ Y) (e : X ⟶ I) (m : I ⟶ Y) : Prop :=
  ∀ (J : C) (e' : X ⟶ J) (m' : J ⟶ Y), Mono m' → e' ≫ m' = f →
    ∃! t : I ⟶ J, t ≫ m' = m ∧ e ≫ t = e'

/-- The factorization `e ≫ m` of `f` is least among factorizations of `f` through
an epimorphism, in Renard's quotient order: every factorization `e' ≫ m' = f` with
`e'` epi maps by a unique `t` to it, with `e' ≫ t = e` and `t ≫ m = m'`. This is
Renard's coimage as the least quotient factoring `f`. -/
def CoimageUniversalProperty {X Y I : C} (f : X ⟶ Y) (e : X ⟶ I) (m : I ⟶ Y) : Prop :=
  ∀ (J : C) (e' : X ⟶ J) (m' : J ⟶ Y), Epi e' → e' ≫ m' = f →
    ∃! t : J ⟶ I, e' ≫ t = e ∧ t ≫ m = m'

end UniversalProperties

/-- A.VI.2(1): a morphism is an isomorphism exactly when it is both a
monomorphism and an epimorphism. -/
def IsoIffMonoAndEpiStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y), IsIso f ↔ Mono f ∧ Epi f

/-- A.VI.2(4): the actual kernel of the cokernel is the image and the actual
cokernel of the kernel is the coimage. Both canonical factorizations are
epi–mono, the abelian image agrees with `Limits.image f` compatibly with both
maps, and the coimage–image comparison is an isomorphism compatible with both
factor maps. -/
def AbelianImageCoimageStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    Abelian.image.ι f = kernel.ι (cokernel.π f) ∧
    Abelian.coimage.π f = cokernel.π (kernel.ι f) ∧
    ImageUniversalProperty f (Abelian.factorThruImage f) (Abelian.image.ι f) ∧
    (Abelian.imageIsoImage f).hom ≫ Limits.image.ι f = Abelian.image.ι f ∧
    Abelian.factorThruImage f ≫ (Abelian.imageIsoImage f).hom = Limits.factorThruImage f ∧
    CoimageUniversalProperty f (Abelian.coimage.π f) (Abelian.factorThruCoimage f) ∧
    Epi (Abelian.factorThruImage f) ∧ Mono (Abelian.image.ι f) ∧
    Abelian.factorThruImage f ≫ Abelian.image.ι f = f ∧
    Epi (Abelian.coimage.π f) ∧ Mono (Abelian.factorThruCoimage f) ∧
    Abelian.coimage.π f ≫ Abelian.factorThruCoimage f = f ∧
    IsIso (Abelian.coimageImageComparison f) ∧
    Abelian.coimage.π f ≫ Abelian.coimageImageComparison f = Abelian.factorThruImage f ∧
    Abelian.coimageImageComparison f ≫ Abelian.image.ι f = Abelian.factorThruCoimage f

/-- A.VI.2(5): every morphism has an epi–mono factorization; any two are related
by a unique isomorphism compatible with both factor maps; and in any epi–mono
factorization the epimorphism is the coimage and the monomorphism is the image. -/
def EpiMonoFactorizationStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    (∃ (I : C) (e : X ⟶ I) (m : I ⟶ Y), Epi e ∧ Mono m ∧ e ≫ m = f) ∧
    (∀ (I J : C) (e : X ⟶ I) (m : I ⟶ Y) (e' : X ⟶ J) (m' : J ⟶ Y),
      Epi e → Mono m → Epi e' → Mono m' → e ≫ m = f → e' ≫ m' = f →
        ∃! t : I ≅ J, e ≫ t.hom = e' ∧ t.hom ≫ m' = m) ∧
    (∀ (I : C) (e : X ⟶ I) (m : I ⟶ Y), Epi e → Mono m → e ≫ m = f →
      ImageUniversalProperty f e m ∧ CoimageUniversalProperty f e m)

/-- The combined statement family of Renard A.VI.2(1, 4–5). -/
def ImageFactorizationStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  IsoIffMonoAndEpiStatement C ∧ AbelianImageCoimageStatement C ∧
    EpiMonoFactorizationStatement C

end Langlands.Renard
