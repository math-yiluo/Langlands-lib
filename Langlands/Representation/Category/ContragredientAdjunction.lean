import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Category.ExactFunctor

/-!
# The smooth contragredient is self-adjoint on the right

Renard 2026, Lemma I.4.2.1: for smooth representations `A` and `B`,
`Hom_G(A, B~) ≃ Hom_G(B, A~)` naturally, by transposition. In categorical form the
smooth contragredient functor `D : Cᵒᵖ ⥤ C` satisfies `D.rightOp ⊣ D`, with unit and
counit both given by evaluation into the smooth bidual.

When compact open subgroups are cofinal, every smooth complex representation `A`
embeds in its smooth bidual, and `A` is the kernel of the composite
`A~~ ⟶ coker ⟶ coker~~`: a copresentation of `A` by two smooth contragredients.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands

universe uR uG uV

namespace SmoothRep

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Evaluation into the smooth bidual, as a morphism of smooth representations. The
carrier universe contains that of the coefficients, so the bidual lies in the same
category. -/
def bidualHom (A : SmoothRep.{uR, uG, max uR uV} R G) :
    A ⟶ A.contragredient.contragredient :=
  ofHom (show A.representation.IntertwiningMap A.contragredient.contragredient.representation
    from smoothBidual A.isSmooth)

/-- Bidual evaluation of `a` sends a smooth functional `ℓ` to `ℓ a`. -/
theorem smoothDualPairing_bidualHom (A : SmoothRep.{uR, uG, max uR uV} R G) (a : A)
    (ℓ : A.contragredient) :
    smoothDualPairing A.contragredient.representation (hom (bidualHom A) a) ℓ =
      smoothDualPairing A.representation ℓ a := rfl

/-- Bidual evaluation is natural. -/
@[reassoc]
theorem bidualHom_naturality {A B : SmoothRep.{uR, uG, max uR uV} R G} (f : A ⟶ B) :
    f ≫ bidualHom B = bidualHom A ≫ contragredientHom (contragredientHom f) :=
  hom_ext' (smoothBidual_natural A.isSmooth B.isSmooth (hom f)).symm

/-- The triangle identity of bidual evaluation: pulling back the bidual evaluation
of a contragredient along the bidual evaluation is the identity. -/
@[reassoc (attr := simp)]
theorem bidualHom_contragredient_comp (A : SmoothRep.{uR, uG, max uR uV} R G) :
    bidualHom A.contragredient ≫ contragredientHom (bidualHom A) = 𝟙 A.contragredient := by
  apply hom_ext'
  ext ℓ
  rfl

/-- The unit of `D.rightOp ⊣ D`: evaluation into the smooth bidual. -/
def bidualTransformation :
    𝟭 (SmoothRep.{uR, uG, max uR uV} R G) ⟶
      contragredientFunctor.rightOp ⋙ contragredientFunctor where
  app A := bidualHom A
  naturality A B f := by
    change f ≫ bidualHom B = bidualHom A ≫ contragredientHom (contragredientHom f)
    exact bidualHom_naturality f

/-- The counit of `D.rightOp ⊣ D`: the opposite of bidual evaluation. -/
def bidualCotransformation :
    contragredientFunctor ⋙ contragredientFunctor.rightOp ⟶
      𝟭 (SmoothRep.{uR, uG, max uR uV} R G)ᵒᵖ where
  app A := (bidualHom A.unop).op
  naturality A B f := by
    apply Quiver.Hom.unop_inj
    exact (bidualHom_naturality f.unop).symm

/-- Renard 2026, Lemma I.4.2.1, in categorical form: the smooth contragredient
functor is right adjoint to its own opposite. The hom equivalence is transposition:
a morphism `A ⟶ B~` corresponds to `B ⟶ A~`, `b ↦ (a ↦ f(a)(b))`. -/
def contragredientAdjunction :
    (contragredientFunctor (R := R) (G := G)).rightOp ⊣
      contragredientFunctor.{uR, uG, max uR uV} where
  unit := bidualTransformation
  counit := bidualCotransformation
  left_triangle_components A :=
    Quiver.Hom.unop_inj (bidualHom_contragredient_comp.{uR, uG, uV} A)
  right_triangle_components A := bidualHom_contragredient_comp.{uR, uG, uV} A.unop

/-- The transposition formula for the hom equivalence of
`contragredientAdjunction`. -/
theorem contragredientAdjunction_homEquiv_apply
    (B : SmoothRep.{uR, uG, max uR uV} R G) (A : (SmoothRep.{uR, uG, max uR uV} R G)ᵒᵖ)
    (f : (contragredientFunctor (R := R) (G := G)).rightOp.obj B ⟶ A) (b : B) (a : A.unop) :
    smoothDualPairing A.unop.representation
        (hom (contragredientAdjunction.homEquiv B A f) b) a =
      smoothDualPairing B.representation (hom f.unop a) b :=
  rfl

end SmoothRep

namespace SmoothRep

section Complex

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- With cofinal compact open subgroups, bidual evaluation is injective. -/
theorem bidualHom_injective (hG : CompactOpenCofinal G) (A : SmoothRep.{0, uG, uV} ℂ G) :
    Function.Injective (hom (bidualHom A)) :=
  smoothBidual_injective_of_compact_cofinal hG _ A.isSmooth

/-- With cofinal compact open subgroups, bidual evaluation is a monomorphism. -/
theorem mono_bidualHom (hG : CompactOpenCofinal G) (A : SmoothRep.{0, uG, uV} ℂ G) :
    Mono (bidualHom A) :=
  (mono_iff_injective _).2 (bidualHom_injective hG A)

/-- The second map of the bidual copresentation `A ⟶ A~~ ⟶ (A~~/A)~~`: the projection
onto the actual quotient module, followed by bidual evaluation. -/
def bidualCopresentationMap (A : SmoothRep.{0, uG, uV} ℂ G) :
    A.contragredient.contragredient ⟶
      (SmoothRep.cokernel (bidualHom A)).contragredient.contragredient :=
  SmoothRep.cokernelπ (bidualHom A) ≫ bidualHom (SmoothRep.cokernel (bidualHom A))

@[reassoc (attr := simp)]
theorem bidualHom_comp_bidualCopresentationMap (A : SmoothRep.{0, uG, uV} ℂ G) :
    bidualHom A ≫ bidualCopresentationMap A = 0 := by
  rw [bidualCopresentationMap, comp_cokernelπ_assoc, zero_comp]

/-- With cofinal compact open subgroups, every smooth complex representation is the
kernel of the second map of its bidual copresentation. -/
def bidualCopresentationIsLimit (hG : CompactOpenCofinal G) (A : SmoothRep.{0, uG, uV} ℂ G) :
    IsLimit (KernelFork.ofι (bidualHom A) (bidualHom_comp_bidualCopresentationMap A)) :=
  isLimitCokernelπComp _ (bidualHom_injective hG A) _ (bidualHom_injective hG _)

end Complex

end SmoothRep

end Langlands
