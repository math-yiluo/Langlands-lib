import Langlands.Representation.Category.FrobeniusChainAdjunction

/-!
# Second adjointness from the unit of the chain (VI.9.6.3)

Let `L : M(M) ⥤ M(G)` and `R : M(G) ⥤ M(M)` be functors between categories of smooth
complex representations, `D` the smooth contragredient and
`A' : L ⋙ D.rightOp ⊣ D ⋙ R` an adjunction, for instance the chain (VI.9.6.3) of Renard
2026, VI.9.6 (printed p.202, PDF p.208). Its unit at `τ` is a morphism
`τ ⟶ R((L τ)~~)`.

If this unit factors through `R` of bidual evaluation `L τ ⟶ (L τ)~~` for every `τ`, then
`L ⊣ R`, provided `R` is exact and compact open subgroups of `G` are cofinal. The
factorization `η_τ : τ ⟶ R(L τ)` is the unit of the new adjunction. No exactness of `L` is
needed.

The proof has two steps. First, the factorization makes `g ↦ η_τ ≫ R g` equal to the chain
bijection `Hom_G(L τ, V~) ≃ Hom_M(τ, R(V~))` on smooth contragredients. Second, a unit
`η` with this bijectivity on contragredients has it on every smooth `π`, through the
copresentation `0 → π → π~~ → (π~~/π)~~`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.SmoothRep

universe uG uV uM uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [Group M] [TopologicalSpace M]
  {L : SmoothRep.{0, uM, uW} ℂ M ⥤ SmoothRep.{0, uG, uV} ℂ G}
  {R : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uM, uW} ℂ M}

section UnitForm

/-- A natural transformation `η : 𝟭 ⟶ L ⋙ R` for which `g ↦ η_τ ≫ R g` is bijective on
morphisms into smooth contragredients is bijective on morphisms into every smooth
representation, when `R` is exact and compact open subgroups of `G` are cofinal. -/
theorem unitHom_bijective (hG : CompactOpenCofinal G) (hR : PreservesShortExact R)
    (η : 𝟭 (SmoothRep.{0, uM, uW} ℂ M) ⟶ L ⋙ R)
    (hbij : ∀ (τ : SmoothRep.{0, uM, uW} ℂ M) (V : SmoothRep.{0, uG, uV} ℂ G),
      Function.Bijective (fun g : L.obj τ ⟶ V.contragredient => η.app τ ≫ R.map g))
    (τ : SmoothRep.{0, uM, uW} ℂ M) (π : SmoothRep.{0, uG, uV} ℂ G) :
    Function.Bijective (fun g : L.obj τ ⟶ π => η.app τ ≫ R.map g) := by
  have := hR.preservesZeroMorphisms
  have hι := mono_bidualHom hG π
  have hRι : Mono (R.map (bidualHom.{0, uG, uV} π)) :=
    (mono_iff_injective _).2 (hR.injective_map _ (bidualHom_injective hG π))
  refine ⟨fun g₁ g₂ h => ?_, fun k => ?_⟩
  · dsimp only at h
    apply (cancel_mono (bidualHom.{0, uG, uV} π)).1
    apply (hbij τ π.contragredient).1
    dsimp only
    rw [Functor.map_comp, Functor.map_comp, reassoc_of% h]
  · obtain ⟨h, hh⟩ := (hbij τ π.contragredient).2 (k ≫ R.map (bidualHom.{0, uG, uV} π))
    dsimp only at hh
    have hq : h ≫ bidualCopresentationMap π = 0 := by
      apply (hbij τ (SmoothRep.cokernel (bidualHom.{0, uG, uV} π)).contragredient).1
      dsimp only
      rw [Functor.map_comp, reassoc_of% hh, ← Functor.map_comp,
        bidualHom_comp_bidualCopresentationMap, Functor.map_zero, Functor.map_zero,
        comp_zero, comp_zero]
    obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' (bidualCopresentationIsLimit hG π) h hq
    refine ⟨l, ?_⟩
    apply (cancel_mono (R.map (bidualHom.{0, uG, uV} π))).1
    dsimp only
    rw [Category.assoc, ← Functor.map_comp]
    exact (congrArg (fun x => η.app τ ≫ R.map x) hl).trans hh

/-- The adjunction `L ⊣ R` with unit `η`, for a natural transformation `η : 𝟭 ⟶ L ⋙ R`
such that `g ↦ η_τ ≫ R g` is bijective on morphisms into smooth contragredients. -/
def adjunctionOfDualUnit (hG : CompactOpenCofinal G) (hR : PreservesShortExact R)
    (η : 𝟭 (SmoothRep.{0, uM, uW} ℂ M) ⟶ L ⋙ R)
    (hbij : ∀ (τ : SmoothRep.{0, uM, uW} ℂ M) (V : SmoothRep.{0, uG, uV} ℂ G),
      Function.Bijective (fun g : L.obj τ ⟶ V.contragredient => η.app τ ≫ R.map g)) :
    L ⊣ R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun τ π => Equiv.ofBijective _ (unitHom_bijective hG hR η hbij τ π)
      homEquiv_naturality_left_symm := fun {τ' τ π} f g => by
        have hn : η.app τ' ≫ R.map (L.map f) = f ≫ η.app τ := (η.naturality f).symm
        rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply, Functor.map_comp,
          ← Category.assoc, hn, Category.assoc]
        congr 1
        exact ((Equiv.ofBijective _ (unitHom_bijective hG hR η hbij τ π)).apply_symm_apply
          g).symm
      homEquiv_naturality_right := fun {τ π π'} f g => by
        change η.app τ ≫ R.map (f ≫ g) = (η.app τ ≫ R.map f) ≫ R.map g
        rw [Functor.map_comp, Category.assoc] }

/-- The unit of `adjunctionOfDualUnit` is `η`. -/
theorem adjunctionOfDualUnit_unit_app (hG : CompactOpenCofinal G) (hR : PreservesShortExact R)
    (η : 𝟭 (SmoothRep.{0, uM, uW} ℂ M) ⟶ L ⋙ R)
    (hbij : ∀ (τ : SmoothRep.{0, uM, uW} ℂ M) (V : SmoothRep.{0, uG, uV} ℂ G),
      Function.Bijective (fun g : L.obj τ ⟶ V.contragredient => η.app τ ≫ R.map g))
    (τ : SmoothRep.{0, uM, uW} ℂ M) :
    (adjunctionOfDualUnit hG hR η hbij).unit.app τ = η.app τ := by
  change η.app τ ≫ R.map (𝟙 (L.obj τ)) = η.app τ
  rw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

end UnitForm

section ChainUnit

/-- If `η₀ : τ ⟶ R(L τ)` lifts the unit of `A'` at `τ` through `R` of bidual evaluation,
then `η₀ ≫ R g` is the image under `A'` of the transpose of `g : L τ ⟶ V~` by Lemma
I.4.2.1. -/
theorem comp_map_contragredientAdjunction_homEquiv
    (A' : L ⋙ contragredientFunctor.{0, uG, uV}.rightOp ⊣
      contragredientFunctor.{0, uG, uV} ⋙ R)
    {τ : SmoothRep.{0, uM, uW} ℂ M} (η₀ : τ ⟶ R.obj (L.obj τ))
    (hη₀ : η₀ ≫ R.map (bidualHom.{0, uG, uV} (L.obj τ)) = A'.unit.app τ)
    (V : SmoothRep.{0, uG, uV} ℂ G)
    (t : contragredientFunctor.{0, uG, uV}.rightOp.obj (L.obj τ) ⟶ Opposite.op V) :
    η₀ ≫ R.map (contragredientAdjunction.{0, uG, uV}.homEquiv (L.obj τ) (Opposite.op V) t) =
      A'.homEquiv τ (Opposite.op V) t := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← hη₀, Functor.map_comp]
  exact (Category.assoc _ _ _).symm

/-- If `η₀` lifts the unit of `A'` at `τ` through `R` of bidual evaluation, then
`g ↦ η₀ ≫ R g` is bijective on morphisms `L τ ⟶ V~` into smooth contragredients. -/
theorem comp_map_bijective_of_unit
    (A' : L ⋙ contragredientFunctor.{0, uG, uV}.rightOp ⊣
      contragredientFunctor.{0, uG, uV} ⋙ R)
    {τ : SmoothRep.{0, uM, uW} ℂ M} (η₀ : τ ⟶ R.obj (L.obj τ))
    (hη₀ : η₀ ≫ R.map (bidualHom.{0, uG, uV} (L.obj τ)) = A'.unit.app τ)
    (V : SmoothRep.{0, uG, uV} ℂ G) :
    Function.Bijective (fun g : L.obj τ ⟶ V.contragredient => η₀ ≫ R.map g) := by
  have h : (fun g : L.obj τ ⟶ V.contragredient => η₀ ≫ R.map g) =
      (A'.homEquiv τ (Opposite.op V)) ∘
        (contragredientAdjunction.{0, uG, uV}.homEquiv (L.obj τ) (Opposite.op V)).symm := by
    funext g
    have hg := comp_map_contragredientAdjunction_homEquiv A' η₀ hη₀ V
      ((contragredientAdjunction.{0, uG, uV}.homEquiv (L.obj τ) (Opposite.op V)).symm g)
    exact (congrArg (fun x : L.obj τ ⟶ V.contragredient => η₀ ≫ R.map x)
      ((contragredientAdjunction.{0, uG, uV}.homEquiv (L.obj τ) (Opposite.op V)).apply_symm_apply
        g).symm).trans hg
  rw [h]
  exact (A'.homEquiv _ _).bijective.comp (Equiv.bijective _)

/-- Lifts of the units of `A'` through `R` of bidual evaluation are natural, when `R`
preserves injectivity (here: `R` exact) and compact open subgroups of `G` are cofinal. -/
theorem unitLift_naturality (hG : CompactOpenCofinal G) (hR : PreservesShortExact R)
    (A' : L ⋙ contragredientFunctor.{0, uG, uV}.rightOp ⊣
      contragredientFunctor.{0, uG, uV} ⋙ R)
    (η₀ : ∀ τ : SmoothRep.{0, uM, uW} ℂ M, τ ⟶ R.obj (L.obj τ))
    (hη₀ : ∀ τ, η₀ τ ≫ R.map (bidualHom.{0, uG, uV} (L.obj τ)) = A'.unit.app τ)
    {τ τ' : SmoothRep.{0, uM, uW} ℂ M} (h : τ ⟶ τ') :
    h ≫ η₀ τ' = η₀ τ ≫ R.map (L.map h) := by
  have hRι : Mono (R.map (bidualHom.{0, uG, uV} (L.obj τ'))) :=
    (mono_iff_injective _).2 (hR.injective_map _ (bidualHom_injective hG _))
  apply (cancel_mono (R.map (bidualHom.{0, uG, uV} (L.obj τ')))).1
  rw [Category.assoc, hη₀, Category.assoc, ← R.map_comp, bidualHom_naturality, R.map_comp,
    ← Category.assoc, hη₀]
  exact A'.unit.naturality h

/-- The adjunction `L ⊣ R` whose unit is a natural family `η₀` of lifts of the units of
`A' : L ⋙ D.rightOp ⊣ D ⋙ R` through `R` of bidual evaluation. -/
def adjunctionOfChainUnit (hG : CompactOpenCofinal G) (hR : PreservesShortExact R)
    (A' : L ⋙ contragredientFunctor.{0, uG, uV}.rightOp ⊣
      contragredientFunctor.{0, uG, uV} ⋙ R)
    (η₀ : ∀ τ : SmoothRep.{0, uM, uW} ℂ M, τ ⟶ R.obj (L.obj τ))
    (hη₀ : ∀ τ, η₀ τ ≫ R.map (bidualHom.{0, uG, uV} (L.obj τ)) = A'.unit.app τ) :
    L ⊣ R :=
  adjunctionOfDualUnit hG hR
    { app := η₀
      naturality := fun _ _ h => unitLift_naturality hG hR A' η₀ hη₀ h }
    (fun τ V => comp_map_bijective_of_unit A' (η₀ τ) (hη₀ τ) V)

/-- The unit of `adjunctionOfChainUnit` is `η₀`. -/
theorem adjunctionOfChainUnit_unit_app (hG : CompactOpenCofinal G)
    (hR : PreservesShortExact R)
    (A' : L ⋙ contragredientFunctor.{0, uG, uV}.rightOp ⊣
      contragredientFunctor.{0, uG, uV} ⋙ R)
    (η₀ : ∀ τ : SmoothRep.{0, uM, uW} ℂ M, τ ⟶ R.obj (L.obj τ))
    (hη₀ : ∀ τ, η₀ τ ≫ R.map (bidualHom.{0, uG, uV} (L.obj τ)) = A'.unit.app τ)
    (τ : SmoothRep.{0, uM, uW} ℂ M) :
    (adjunctionOfChainUnit hG hR A' η₀ hη₀).unit.app τ = η₀ τ :=
  adjunctionOfDualUnit_unit_app hG hR _ _ τ

/-- `L ⊣ R` from an adjunction `A' : L ⋙ D.rightOp ⊣ D ⋙ R` whose unit at every `τ`
factors through `R` of bidual evaluation `L τ ⟶ (L τ)~~`, when `R` is exact and compact
open subgroups of `G` are cofinal. -/
theorem nonempty_adjunction_of_chainUnit (hG : CompactOpenCofinal G)
    (hR : PreservesShortExact R)
    (A' : L ⋙ contragredientFunctor.{0, uG, uV}.rightOp ⊣
      contragredientFunctor.{0, uG, uV} ⋙ R)
    (hU : ∀ τ : SmoothRep.{0, uM, uW} ℂ M, ∃ η₀ : τ ⟶ R.obj (L.obj τ),
      η₀ ≫ R.map (bidualHom.{0, uG, uV} (L.obj τ)) = A'.unit.app τ) :
    Nonempty (L ⊣ R) :=
  ⟨adjunctionOfChainUnit hG hR A' (fun τ => (hU τ).choose) (fun τ => (hU τ).choose_spec)⟩

end ChainUnit

section Frobenius

variable [IsTopologicalGroup M] {r : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uM, uW} ℂ M}

/-- The unit of the chain at `τ`: bidual evaluation of `τ`, the transpose of the counit of
Frobenius reciprocity at `τ~`, the transpose of `r` of `C` at `τ`, and the inverse of `Ψ`
at `(L τ)~`. -/
theorem unit_frobeniusChainAdjunction (F : r ⊣ L)
    (C : L.op ⋙ contragredientFunctor.{0, uG, uV} ≅ contragredientFunctor.{0, uM, uW} ⋙ L)
    (Ψ : contragredientFunctor.{0, uG, uV} ⋙ R ≅ r.op ⋙ contragredientFunctor.{0, uM, uW})
    (τ : SmoothRep.{0, uM, uW} ℂ M) :
    (frobeniusChainAdjunction F C Ψ).unit.app τ =
      bidualHom.{0, uM, uW} τ ≫ contragredientHom (F.counit.app τ.contragredient) ≫
        contragredientHom (r.map (C.hom.app (Opposite.op τ))) ≫
          Ψ.inv.app (Opposite.op (L.obj τ).contragredient) := by
  simp only [frobeniusChainAdjunction, Adjunction.ofNatIsoRight, Adjunction.ofNatIsoLeft,
    Adjunction.comp_unit_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc]
  rfl

/-- Renard 2026, VI.9.6 (printed p.202): `L ⊣ R` from Frobenius reciprocity `F : r ⊣ L`,
`C : (L τ)~ ≅ L(τ~)` and `Ψ : R(V~) ≅ (r V)~`, for exact `R`, when the unit of the chain at
every `τ` factors through `R` of bidual evaluation `L τ ⟶ (L τ)~~`. -/
theorem nonempty_adjunction_of_frobeniusChain_unit (hG : CompactOpenCofinal G)
    (hR : PreservesShortExact R) (F : r ⊣ L)
    (C : L.op ⋙ contragredientFunctor.{0, uG, uV} ≅ contragredientFunctor.{0, uM, uW} ⋙ L)
    (Ψ : contragredientFunctor.{0, uG, uV} ⋙ R ≅ r.op ⋙ contragredientFunctor.{0, uM, uW})
    (hU : ∀ τ : SmoothRep.{0, uM, uW} ℂ M, ∃ η₀ : τ ⟶ R.obj (L.obj τ),
      η₀ ≫ R.map (bidualHom.{0, uG, uV} (L.obj τ)) =
        bidualHom.{0, uM, uW} τ ≫ contragredientHom (F.counit.app τ.contragredient) ≫
          contragredientHom (r.map (C.hom.app (Opposite.op τ))) ≫
            Ψ.inv.app (Opposite.op (L.obj τ).contragredient)) :
    Nonempty (L ⊣ R) :=
  nonempty_adjunction_of_chainUnit hG hR (frobeniusChainAdjunction F C Ψ) fun τ => by
    obtain ⟨η₀, hη₀⟩ := hU τ
    exact ⟨η₀, hη₀.trans (unit_frobeniusChainAdjunction F C Ψ τ).symm⟩

end Frobenius

end Langlands.SmoothRep
