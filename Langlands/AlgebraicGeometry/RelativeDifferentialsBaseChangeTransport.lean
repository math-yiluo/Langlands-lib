import Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChange
import Langlands.AlgebraicGeometry.RelativeDifferentialsOpenImmersionStatement
import Langlands.AlgebraicGeometry.Modules.SectionLocusComparison
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs

/-! # Composition and transport for canonical differential square maps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

namespace Langlands.Scheme

variable {X Y Z S T U : AlgebraicGeometry.Scheme.{u}}

private lemma pullbackHomEquiv_comp (g : X ⟶ Y) (h : Y ⟶ Z)
    (A : Z.Modules) (B : Y.Modules) (M : X.Modules)
    (α : (pullback h).obj A ⟶ B) (β : (pullback g).obj B ⟶ M) :
    (pullbackPushforwardAdjunction (g ≫ h)).homEquiv A M
      ((pullbackComp g h).inv.app A ≫ (pullback g).map α ≫ β) =
        (pullbackPushforwardAdjunction h).homEquiv A B α ≫
          (pushforward h).map ((pullbackPushforwardAdjunction g).homEquiv B M β) ≫
            (pushforwardComp g h).hom.app M := by
  rw [Langlands.Scheme.Modules.homEquiv_conjugate
    ((pullbackPushforwardAdjunction h).comp (pullbackPushforwardAdjunction g))
    (pullbackPushforwardAdjunction (g ≫ h)) (pullbackComp g h).inv]
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_homEquiv]
  change (pullbackPushforwardAdjunction h).homEquiv _ _
    ((pullbackPushforwardAdjunction g).homEquiv _ _ ((pullback g).map α ≫ β)) ≫ _ = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Category.assoc]


lemma relativeDifferentialsSquarePushforwardMap_app_D
    (g : X ⟶ Y) (b : T ⟶ S) {fX : X ⟶ T} {fY : Y ⟶ S}
    (w : g ≫ fY = fX ≫ b) (V : Y.Opens) (a : Γ(Y, V)) :
    (relativeDifferentialsSquarePushforwardMap g b w).app V
      ((relativeDifferentialsDerivation fY).app V a) =
    (relativeDifferentialsDerivation fX).app (g ⁻¹ᵁ V) (g.app V a) := by
  rw [← relativeDifferentialsSquareMap_adjoint]
  exact relativeDifferentialsSquareMap_adjoint_app g b w V a

lemma relativeDifferentialsSquarePushforwardMap_comp
    (g : X ⟶ Y) (h : Y ⟶ Z) (b : U ⟶ T) (c : T ⟶ S)
    {fX : X ⟶ U} {fY : Y ⟶ T} {fZ : Z ⟶ S}
    (wg : g ≫ fY = fX ≫ b) (wh : h ≫ fZ = fY ≫ c) :
    relativeDifferentialsSquarePushforwardMap h c wh ≫
      (pushforward h).map (relativeDifferentialsSquarePushforwardMap g b wg) ≫
        (pushforwardComp g h).hom.app (relativeDifferentials fX) =
    relativeDifferentialsSquarePushforwardMap (g ≫ h) (b ≫ c)
      (by rw [Category.assoc, wh, ← Category.assoc, wg, Category.assoc]) := by
  apply relativeDifferentials_hom_ext fZ
  ext V a
  change Γ(Z, V.unop) at a
  change (RelativeDerivation.postcomp (relativeDifferentialsDerivation fZ) _).app V.unop a =
    (RelativeDerivation.postcomp (relativeDifferentialsDerivation fZ) _).app V.unop a
  simp only [RelativeDerivation.postcomp_app, Hom.comp_app,
    pushforward_map_app, pushforwardComp_hom_app_app]
  change (relativeDifferentialsSquarePushforwardMap g b wg).app (h ⁻¹ᵁ V.unop)
    ((relativeDifferentialsSquarePushforwardMap h c wh).app V.unop
      ((relativeDifferentialsDerivation fZ).app V.unop a)) = _
  rw [relativeDifferentialsSquarePushforwardMap_app_D,
    relativeDifferentialsSquarePushforwardMap_app_D,
    relativeDifferentialsSquarePushforwardMap_app_D]
  rfl

lemma relativeDifferentialsSquareMap_comp
    (g : X ⟶ Y) (h : Y ⟶ Z) (b : U ⟶ T) (c : T ⟶ S)
    {fX : X ⟶ U} {fY : Y ⟶ T} {fZ : Z ⟶ S}
    (wg : g ≫ fY = fX ≫ b) (wh : h ≫ fZ = fY ≫ c) :
    (pullbackComp g h).inv.app (relativeDifferentials fZ) ≫
      (pullback g).map (relativeDifferentialsSquareMap h c wh) ≫
        relativeDifferentialsSquareMap g b wg =
    relativeDifferentialsSquareMap (g ≫ h) (b ≫ c)
      (by rw [Category.assoc, wh, ← Category.assoc, wg, Category.assoc]) := by
  apply ((pullbackPushforwardAdjunction (g ≫ h)).homEquiv _ _).injective
  rw [pullbackHomEquiv_comp, relativeDifferentialsSquareMap_adjoint,
    relativeDifferentialsSquareMap_adjoint, relativeDifferentialsSquareMap_adjoint,
    relativeDifferentialsSquarePushforwardMap_comp]

lemma relativeDifferentials_isIso_of_openCover_pullback {X : AlgebraicGeometry.Scheme.{u}}
    (𝒰 : X.OpenCover) {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ i, IsIso ((pullback (𝒰.f i)).map φ)) : IsIso φ := by
  apply (Langlands.SchemeModule.isIso_iff_stalk_isIso φ).mpr
  intro x
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  have : IsIso ((restrictFunctor (𝒰.f i)).map φ) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback (𝒰.f i)) φ).mpr (h i)
  exact (NatIso.isIso_map_iff (restrictStalkNatIso (𝒰.f i) y) φ).mp
    (by
      change IsIso ((TopCat.Presheaf.stalkFunctor Ab y).map
        ((toPresheaf _).map ((restrictFunctor (𝒰.f i)).map φ)))
      infer_instance)

lemma relativeDifferentialsSquareMap_congr {X X' S S' : AlgebraicGeometry.Scheme.{u}}
    {g g' : X' ⟶ X} {b b' : S' ⟶ S} {f : X ⟶ S} {f' : X' ⟶ S'}
    (hg : g = g') (hb : b = b') (w : g ≫ f = f' ≫ b)
    (w' : g' ≫ f = f' ≫ b') :
    (pullbackCongr hg).hom.app (relativeDifferentials f) ≫
      relativeDifferentialsSquareMap g' b' w' = relativeDifferentialsSquareMap g b w := by
  subst g'
  subst b'
  simp [pullbackCongr]

/-- Transfer an invertible square map through an isomorphic model of the fiber product. -/
lemma relativeDifferentialsBaseChangeMap_isIso_of_square
    (hopen : RelativeDifferentialsOpenImmersionIsIsoStatement.{u})
    {X₀ X S T : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ S) (b : T ⟶ S) (i : X₀ ⟶ X) (q₀ : X₀ ⟶ T)
    (w : i ≫ f = q₀ ≫ b)
    (l : X₀ ⟶ Limits.pullback f b) [IsIso l]
    (hp : l ≫ Limits.pullback.fst f b = i)
    (hq : l ≫ Limits.pullback.snd f b = q₀)
    [IsIso (relativeDifferentialsSquareMap i b w)] :
    IsIso (relativeDifferentialsBaseChangeMap f b) := by
  let p := Limits.pullback.fst f b
  let q := Limits.pullback.snd f b
  have wl : l ≫ q = q₀ ≫ 𝟙 T := by simpa using hq
  have : IsIso (relativeDifferentialsSquareMap l (𝟙 T) wl) :=
    hopen _ _ _ _ q q₀ l (𝟙 T) inferInstance inferInstance wl
  have hcomp := relativeDifferentialsSquareMap_comp l p (𝟙 T) b wl Limits.pullback.condition
  have hcongr := relativeDifferentialsSquareMap_congr hp (Category.id_comp b)
    (by rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, wl, Category.assoc]) w
  have heq : (pullback l).map (relativeDifferentialsBaseChangeMap f b) ≫
        relativeDifferentialsSquareMap l (𝟙 T) wl =
      (pullbackComp l p).hom.app (relativeDifferentials f) ≫
        (pullbackCongr hp).hom.app (relativeDifferentials f) ≫
          relativeDifferentialsSquareMap i b w := by
    apply (cancel_epi ((pullbackComp l p).inv.app (relativeDifferentials f))).mp
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    simp only [Category.assoc, relativeDifferentialsBaseChangeMap]
    rw [hcomp, hcongr]
  have : IsIso ((pullback l).map (relativeDifferentialsBaseChangeMap f b) ≫
      relativeDifferentialsSquareMap l (𝟙 T) wl) := by
    rw [heq]
    infer_instance
  have hmap : IsIso ((pullback l).map (relativeDifferentialsBaseChangeMap f b)) :=
    IsIso.of_isIso_comp_right _ (relativeDifferentialsSquareMap l (𝟙 T) wl)
  exact relativeDifferentials_isIso_of_openCover_pullback (AlgebraicGeometry.Scheme.coverOfIsIso.{0} l) _
    (fun _ => hmap)

end Langlands.Scheme
