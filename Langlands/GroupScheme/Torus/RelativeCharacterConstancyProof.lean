import Langlands.GroupScheme.Cartier.FiniteDualGeometry
import Langlands.GroupScheme.Torus.RelativeCharacterConstancyStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeQuasiIsotrivialProof
import Langlands.GroupScheme.Cartier.CharacterFamilyEvaluation
import Langlands.GroupScheme.Cartier.DiagonalizableConstant
import Langlands.GroupScheme.Cartier.BaseChange
import Langlands.GroupScheme.RelativeLevi.MultiplicationDescent

/-! # Constant actual relative characters and diagonalizability -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.EtaleLocalSystem
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open RelativeMultiplicativeType Cartier

namespace Cartier

variable {S Y : Scheme.{u}}

private theorem relativeHom_ext_of_evaluation {G H : CommGroupScheme S} {T : Over S}
    {χ ψ : RelativeHom G H T}
    (h : ∀ (V : Over S) (b : V ⟶ T) (x : V ⟶ G.X),
      evaluation (restrict G H b χ) x = evaluation (restrict G H b ψ) x) : χ = ψ := by
  let V : Over S := (Over.map T.hom).obj (testBaseChange T G).X
  let b : V ⟶ T := Over.homMk (pullback.snd G.X.hom T.hom) rfl
  let x : V ⟶ G.X := Over.homMk (pullback.fst G.X.hom T.hom) pullback.condition
  have hid : ((sectionPointsEquiv G V).symm x).left ≫ baseChangeProj G b =
      𝟙 (pullback G.X.hom T.hom) := by
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeProj_fst, sectionPointsEquiv_symm_fst]
      exact (Category.id_comp _).symm
    · rw [Category.assoc, baseChangeProj_snd, sectionPointsEquiv_symm_snd_assoc]
      change 𝟙 (pullback G.X.hom T.hom) ≫ pullback.snd G.X.hom T.hom = _
      rfl
  have hfac : ∀ φ : RelativeHom G H T,
      (evaluation (restrict G H b φ) x).left =
        CommGroupScheme.hom φ ≫ pullback.fst H.X.hom T.hom := by
    intro φ
    rw [evaluation_def, sectionPointsEquiv_left, Over.comp_left, Category.assoc,
      restrict_fst, ← Category.assoc, hid]
    exact Category.id_comp _
  apply relativeHom_ext
  simpa only [hfac] using congrArg CommaMorphism.left (h V b x)

private theorem constant_hom_ext {M N : AddCommGrpCat.{u}} {α β : constant S M ⟶ constant S N}
    (h : ∀ (T : Over S) (m : M),
      α.app (op T) (constantCoefficient M T m) =
        β.app (op T) (constantCoefficient M T m)) : α = β := by
  ext T s
  let V := T.unop
  apply (constantSections S N V).injective
  ext x
  let f := constantSections S M V s
  let U : V.left.Opens := ⟨{y | f y = f x}, f.isLocallyConstant.isOpen_fiber _⟩
  let W : Over S := Over.mk (U.ι ≫ V.hom)
  let b : W ⟶ V := Over.homMk U.ι rfl
  let x' : W.left := ⟨x, rfl⟩
  have hs : (constant S M).map b.op s = constantCoefficient M W (f x) := by
    apply (constantSections S M W).injective
    ext y
    rw [constantSections_map]
    change f y.1 = constantSections S M W (constantCoefficient M W (f x)) y
    rw [show constantSections S M W (constantCoefficient M W (f x)) =
        LocallyConstant.const W.left (f x) from AddEquiv.apply_symm_apply _ _]
    exact y.2
  have hα := ConcreteCategory.congr_hom (α.naturality b.op) s
  have hβ := ConcreteCategory.congr_hom (β.naturality b.op) s
  change α.app (op W) ((constant S M).map b.op s) =
    (constant S N).map b.op (α.app (op V) s) at hα
  change β.app (op W) ((constant S M).map b.op s) =
    (constant S N).map b.op (β.app (op V) s) at hβ
  rw [hs] at hα hβ
  have h' := congrArg (fun t => constantSections S N W t x')
    (hα.symm.trans ((h W (f x)).trans hβ))
  rw [constantSections_map, constantSections_map] at h'
  have hx : b.left x' = x := Scheme.Opens.ι_apply _ _
  rw [hx] at h'
  exact h'

private theorem charactersMap_baseChange {G H : CommGroupScheme S} (b : Y ⟶ S)
    (f : G ⟶ H) :
    Functor.whiskerLeft (Over.map b).op (charactersMap f) ≫ (charactersBaseChangeIso G b).hom =
      (charactersBaseChangeIso H b).hom ≫
        charactersMap ((CommGroupScheme.baseChange b).map f) := by
  ext T χ
  let V := T.unop
  have hnat :
      (CommGroupScheme.baseChange (V.hom ≫ b)).map f ≫ (testBaseChangeAlongIso H b V).hom =
        (testBaseChangeAlongIso G b V).hom ≫
          (CommGroupScheme.baseChange V.hom).map ((CommGroupScheme.baseChange b).map f) := by
    apply Additive.toMul.injective
    exact ((Functor.mapGrpNatIso (Over.pullbackComp V.hom b)) ≪≫
      Functor.mapGrpCompIso).hom.naturality f.toMul
  have hi := congrArg (fun k => (testBaseChangeAlongIso G b V).inv ≫ k ≫
    (testBaseChangeAlongIso H b V).inv) hnat
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] at hi
  change ((testBaseChangeAlongIso G b V).inv ≫
      ((CommGroupScheme.baseChange (V.hom ≫ b)).map f ≫ χ) ≫
        (testBaseChangeAlongIso (Gm S) b V).hom) ≫
          (CommGroupScheme.baseChange V.hom).map (Gm.commBaseChangeIso b).hom =
    (CommGroupScheme.baseChange V.hom).map ((CommGroupScheme.baseChange b).map f) ≫
      (((testBaseChangeAlongIso H b V).inv ≫ χ ≫
        (testBaseChangeAlongIso (Gm S) b V).hom) ≫
          (CommGroupScheme.baseChange V.hom).map (Gm.commBaseChangeIso b).hom)
  simp only [← Category.assoc]
  rw [hi]

open DiagonalizableCharacters

private theorem evaluation_evalChar {M : Type u} [AddCommGroup M] (T : Over S)
    (m : M) (x : T ⟶ (model S M).X) :
    Gm.pointsEquiv S T (characterEvaluation (evalChar T m) x) =
      pointsEquiv S M T x (.ofAdd m) := by
  change Gm.pointsEquiv S T
    (evaluation ((CommGroupScheme.baseChange T.hom).map (globalEval S m)) x) = _
  rw [evaluation_baseChange]
  exact globalEval_apply m T x

private def familyHom (G : CommGroupScheme S) (M : AddCommGrpCat.{u})
    (a : constant S M ⟶ characters G) : G ⟶ model S M :=
  Additive.ofMul (characterFamilyHom G M a)

private theorem charactersMap_familyHom_evalChar (G : CommGroupScheme S) (M : AddCommGrpCat.{u})
    (a : constant S M ⟶ characters G) (T : Over S) (m : M) :
    (charactersMap (familyHom G M a)).app (op T) (evalChar T m) =
      familyCharacter G M a T m := by
  apply relativeHom_ext_of_evaluation
  intro W b x
  apply (Gm.pointsEquiv S W).injective
  let α := charactersMap (familyHom G M a)
  have hnat := ConcreteCategory.congr_hom (α.naturality b.op) (evalChar T m)
  change α.app (op W) ((characters (model S M)).map b.op (evalChar T m)) =
    (characters G).map b.op (α.app (op T) (evalChar T m)) at hnat
  change Gm.pointsEquiv S W
    (characterEvaluation ((characters G).map b.op (α.app (op T) (evalChar T m))) x) =
    Gm.pointsEquiv S W
      (characterEvaluation ((characters G).map b.op (familyCharacter G M a T m)) x)
  rw [← hnat, restrict_evalChar, familyCharacter_restrict]
  change Gm.pointsEquiv S W
    (characterEvaluation ((charactersMap (familyHom G M a)).app (op W) (evalChar W m)) x) = _
  rw [characterEvaluation_precompose, evaluation_evalChar]
  exact characterFamilyHom_evaluation G M a W x m

private theorem charactersMap_familyHom (G : CommGroupScheme S) (M N : AddCommGrpCat.{u})
    (a : constant S M ⟶ characters G) (e : characters G ≅ constant S N) :
    charactersMap (familyHom G M a) = (charactersIso S M).hom ≫ a := by
  have hcomp : (charactersIso S M).inv ≫ charactersMap (familyHom G M a) = a := by
    apply (cancel_mono e.hom).1
    apply constant_hom_ext
    intro T m
    change e.hom.app (op T)
      ((charactersMap (familyHom G M a)).app (op T)
        ((charactersIso S M).inv.app (op T) (constantCoefficient M T m))) =
      e.hom.app (op T) (familyCharacter G M a T m)
    have hm : (charactersIso S M).inv.app (op T) (constantCoefficient M T m) =
        evalChar T m := charactersIso_inv_app_const T m
    rw [hm, charactersMap_familyHom_evalChar]
  calc
    charactersMap (familyHom G M a) =
        (charactersIso S M).hom ≫
          ((charactersIso S M).inv ≫ charactersMap (familyHom G M a)) := by simp
    _ = (charactersIso S M).hom ≫ a := by rw [hcomp]

private theorem charactersMap_injective_model {G : CommGroupScheme S} {M : Type u}
    [AddCommGroup M] {f g : G ⟶ model S M}
    (h : charactersMap f = charactersMap g) : f = g := by
  apply Additive.toMul.injective
  apply hom_ext_points
  intro T x
  apply (pointsEquiv S M T).injective
  apply MonoidHom.ext
  intro m
  have hm := congrArg (fun a => a.app (op T) (evalChar T m.toAdd)) h
  have he := congrArg (fun χ => Gm.pointsEquiv S T (characterEvaluation χ x)) hm
  simpa only [characterEvaluation_precompose, evaluation_evalChar, ofAdd_toAdd] using he

private theorem isIso_of_charactersMap_model {M N : AddCommGrpCat.{u}}
    (f : model S M ⟶ model S N) [IsIso (charactersMap f)] : IsIso f := by
  let eM := charactersIso S M
  let eN := charactersIso S N
  let a := eM.inv ≫ inv (charactersMap f)
  let g := familyHom (model S N) M a
  have hg : charactersMap g = inv (charactersMap f) := by
    change charactersMap (familyHom (model S N) M a) = _
    rw [charactersMap_familyHom _ _ _ _ eN]
    change eM.hom ≫ eM.inv ≫ inv (charactersMap f) = _
    simp
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply charactersMap_injective_model
    simp [charactersMap_comp, hg]
  · apply charactersMap_injective_model
    simp [charactersMap_comp, hg]

private theorem isIso_of_charactersMap_of_split {G H : CommGroupScheme S}
    (f : G ⟶ H) {M N : AddCommGrpCat.{u}}
    (p : G ≅ model S M) (q : H ≅ model S N)
    [IsIso (charactersMap f)] : IsIso f := by
  let g := p.inv ≫ f ≫ q.hom
  let : IsIso (charactersMap p.inv) := (Langlands.GroupScheme.Cartier.FiniteDual.charactersIso p.symm).isIso_hom
  let : IsIso (charactersMap q.hom) := (Langlands.GroupScheme.Cartier.FiniteDual.charactersIso q).isIso_hom
  let : IsIso (charactersMap g) := by
    change IsIso (charactersMap (p.inv ≫ f ≫ q.hom))
    rw [charactersMap_comp, charactersMap_comp]
    infer_instance
  let : IsIso g := isIso_of_charactersMap_model g
  have h : IsIso (p.hom ≫ g ≫ q.inv) := inferInstance
  simpa [g] using h

end Cartier

open Cartier.DiagonalizableCharacters

/-- A group of multiplicative type is diagonalizable exactly when its actual character
presheaf is constant with a finitely generated coefficient group. -/
theorem relativeCharacterConstancy : RelativeCharacterConstancyStatement.{u} := by
  intro S H hH
  let G := hH.commGroupScheme
  constructor
  · rintro ⟨M, hM, hfg, ⟨e⟩⟩
    let : AddCommGroup M := hM
    let e' : G ≅ model S M := CommGroupScheme.isoOfGroupIso e
    exact ⟨AddCommGrpCat.of M, hfg, ⟨(Langlands.GroupScheme.Cartier.FiniteDual.charactersIso e').symm ≪≫ charactersIso S M⟩⟩
  · rintro ⟨M, hfg, ⟨e⟩⟩
    let f := familyHom G M e.inv
    let : IsIso (charactersMap f) := by
      change IsIso (charactersMap (familyHom G M e.inv))
      rw [charactersMap_familyHom _ _ _ _ e]
      infer_instance
    obtain ⟨𝒰, h𝒰⟩ := multiplicativeTypeQuasiIsotrivial.1 S H hH
    have hlocal : ∀ i, IsIso ((Over.pullback (𝒰.f i)).map f.toMul.hom.hom) := by
      intro i
      let b := 𝒰.f i
      let fb := (CommGroupScheme.baseChange b).map f
      let : IsIso ((charactersBaseChangeIso (model S M) b).hom ≫ charactersMap fb) := by
        change IsIso ((charactersBaseChangeIso (model S M) b).hom ≫
          charactersMap ((CommGroupScheme.baseChange b).map f))
        rw [← charactersMap_baseChange b f]
        infer_instance
      let : IsIso (charactersMap fb) :=
        IsIso.of_isIso_comp_left (charactersBaseChangeIso (model S M) b).hom _
      obtain ⟨N, hN, _, ⟨p⟩⟩ := h𝒰 i
      let : AddCommGroup N := hN
      let p' : (CommGroupScheme.baseChange b).obj G ≅
          model (𝒰.X i) (AddCommGrpCat.of N) := CommGroupScheme.isoOfGroupIso p
      let q' : (CommGroupScheme.baseChange b).obj (model S M) ≅
          model (𝒰.X i) M := CommGroupScheme.isoOfGroupIso (diagonalizableBaseChangeIso b M)
      let : IsIso fb := isIso_of_charactersMap_of_split fb p' q'
      let : IsIso fb.toMul :=
        ⟨⟨(inv fb).toMul, congrArg Additive.toMul (IsIso.hom_inv_id fb),
          congrArg Additive.toMul (IsIso.inv_hom_id fb)⟩⟩
      exact (Grp.forget _).map_isIso fb.toMul
    let : IsIso ((Mon.forget _).map f.toMul.hom) :=
      RelativeLevi.isIso_of_etaleCover 𝒰 f.toMul.hom.hom hlocal
    let : IsIso ((Grp.forget₂Mon _).map f.toMul) :=
      isIso_of_reflects_iso f.toMul.hom (Mon.forget _)
    let : IsIso f.toMul := isIso_of_reflects_iso f.toMul (Grp.forget₂Mon _)
    exact ⟨M, inferInstance, hfg, ⟨asIso f.toMul⟩⟩

end Langlands.GroupScheme
