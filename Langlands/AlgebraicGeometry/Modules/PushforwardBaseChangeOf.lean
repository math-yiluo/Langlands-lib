import Langlands.AlgebraicGeometry.Modules.AffineDirectImageBaseChange

/-!
# The degree-zero base-change comparison for a module map into a pushforward

For a commutative square `p ≫ f = f' ≫ b` of schemes and an arbitrary morphism of modules
`a : P ⟶ p_* N`, `pushforwardBaseChangeOf f b f' p w a : b^* f_* P ⟶ f'_* N` is the adjunct
of `f_* a` followed by the pushforward square comparison `f_* p_* ≅ b_* f'_*`. For `a` the unit
of `p` it is the published `pushforwardBaseChange` (`pushforwardBaseChangeOf_unit`). Over
spectra, the corresponding ordinary sections, scalar-linear and tilde maps generalize
`sectionsBaseChangeMap`, `scalarSectionsBaseChangeMap` and `affineDirectImageTildeMap`.
No cartesianness, flatness, quasi-coherence or invertibility is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Scheme.Modules

section Square

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
  (p : X' ⟶ X) (w : p ≫ f = f' ≫ b)

/-- The base-change comparison `b^* f_* P ⟶ f'_* N` of a morphism `a : P ⟶ p_* N`: the adjunct
along `b` of `f_* a` followed by the pushforward comparison `f_* p_* N ≅ b_* f'_* N`. -/
def pushforwardBaseChangeOf {P : X.Modules} {N : X'.Modules}
    (a : P ⟶ (Scheme.Modules.pushforward p).obj N) :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pushforward f).obj P) ⟶
      (Scheme.Modules.pushforward f').obj N :=
  ((Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _).symm
    ((Scheme.Modules.pushforward f).map a ≫ (pushforwardSquareIso b f f' p w).hom.app N)

/-- The adjunct along `b` of the comparison is `f_* a` followed by the square comparison. -/
@[simp]
lemma pushforwardBaseChangeOf_homEquiv {P : X.Modules} {N : X'.Modules}
    (a : P ⟶ (Scheme.Modules.pushforward p).obj N) :
    (Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _
        (pushforwardBaseChangeOf f b f' p w a) =
      (Scheme.Modules.pushforward f).map a ≫ (pushforwardSquareIso b f f' p w).hom.app N := by
  simp only [pushforwardBaseChangeOf, Equiv.apply_symm_apply]

/-- At the unit of `p` the comparison is the published base change map. -/
theorem pushforwardBaseChangeOf_unit (P : X.Modules) :
    pushforwardBaseChangeOf f b f' p w
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app P) =
      pushforwardBaseChange b f f' p w P :=
  rfl

/-- The published base change map followed by `f'_* ψ` is the comparison of the unit of `p`
followed by `p_* ψ`. -/
theorem pushforwardBaseChange_comp_pushforward_map (P : X.Modules) {N : X'.Modules}
    (ψ : (Scheme.Modules.pullback p).obj P ⟶ N) :
    pushforwardBaseChange b f f' p w P ≫ (Scheme.Modules.pushforward f').map ψ =
      pushforwardBaseChangeOf f b f' p w
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app P ≫
          (Scheme.Modules.pushforward p).map ψ) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, ← pushforwardBaseChangeOf_unit,
    pushforwardBaseChangeOf_homEquiv, pushforwardBaseChangeOf_homEquiv]
  have hc := (pushforwardSquareIso b f f' p w).hom.naturality ψ
  simp only [Functor.comp_map] at hc
  rw [Functor.map_comp, Category.assoc, Category.assoc, hc]

end Square

section Spectra

variable {X X' : Scheme.{u}} {R T : CommRingCat.{u}}
  (φ : R ⟶ T) (f : X ⟶ Spec R) (f' : X' ⟶ Spec T)
  (g : X' ⟶ X) (w : g ≫ f = f' ≫ Spec.map φ)

/-- The map on ordinary relative sections induced by `a : P ⟶ g_* N` and the commuting
square: `Γ(a)`, then the composition and base-ring identifications. -/
def sectionsBaseChangeMapOf {P : X.Modules} {N : X'.Modules}
    (a : P ⟶ (Scheme.Modules.pushforward g).obj N) :
    (relativeGlobalSections f).obj P ⟶
      (ModuleCat.restrictScalars φ.hom).obj ((relativeGlobalSections f').obj N) :=
  (relativeGlobalSections f).map a ≫
    (relativeGlobalSectionsCompIso g f).hom.app N ≫
    (relativeGlobalSectionsBaseRingIso φ (g ≫ f) f' w).inv.app N

/-- The scalar-linear adjunct of the ordinary relative sections map of `a`. -/
def scalarSectionsBaseChangeMapOf {P : X.Modules} {N : X'.Modules}
    (a : P ⟶ (Scheme.Modules.pushforward g).obj N) :
    (ModuleCat.extendScalars φ.hom).obj ((relativeGlobalSections f).obj P) ⟶
      (relativeGlobalSections f').obj N :=
  ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm
    (sectionsBaseChangeMapOf φ f f' g w a)

/-- The scalar sections map of `a` followed by the tilde counit of `f'_* N`. -/
def affineDirectImageTildeMapOf {P : X.Modules} {N : X'.Modules}
    (a : P ⟶ (Scheme.Modules.pushforward g).obj N) :
    tilde ((ModuleCat.extendScalars φ.hom).obj ((relativeGlobalSections f).obj P)) ⟶
      (Scheme.Modules.pushforward f').obj N :=
  tilde.map (scalarSectionsBaseChangeMapOf φ f f' g w a) ≫
    ((Scheme.Modules.pushforward f').obj N).fromTildeΓ

/-- At the unit of `g` the ordinary sections map is the published one. -/
lemma sectionsBaseChangeMapOf_unit (M : X.Modules) :
    sectionsBaseChangeMapOf φ f f' g w
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) =
      sectionsBaseChangeMap φ f f' g w M :=
  rfl

/-- At the unit of `g` the scalar sections map is the published one. -/
lemma scalarSectionsBaseChangeMapOf_unit (M : X.Modules) :
    scalarSectionsBaseChangeMapOf φ f f' g w
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) =
      scalarSectionsBaseChangeMap φ f f' g w M :=
  rfl

/-- At the unit of `g` the tilde map is the published one. -/
lemma affineDirectImageTildeMapOf_unit (M : X.Modules) :
    affineDirectImageTildeMapOf φ f f' g w
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) =
      affineDirectImageTildeMap φ f f' g w M :=
  rfl

/-- The ordinary sections map applies `a` on top sections. -/
lemma sectionsBaseChangeMapOf_apply {P : X.Modules} {N : X'.Modules}
    (a : P ⟶ (Scheme.Modules.pushforward g).obj N) (x : (relativeGlobalSections f).obj P) :
    sectionsBaseChangeMapOf φ f f' g w a x = a.app ⊤ x := by
  rfl

@[simp]
lemma scalarSectionsBaseChangeMapOf_homEquiv {P : X.Modules} {N : X'.Modules}
    (a : P ⟶ (Scheme.Modules.pushforward g).obj N) :
    (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _
        (scalarSectionsBaseChangeMapOf φ f f' g w a) =
      sectionsBaseChangeMapOf φ f f' g w a := by
  simp only [scalarSectionsBaseChangeMapOf, Equiv.apply_symm_apply]

/-- The scalar sections map sends a tensor generator `1 ⊗ x` to `a` on top sections. -/
lemma scalarSectionsBaseChangeMapOf_one_tmul {P : X.Modules} {N : X'.Modules}
    (a : P ⟶ (Scheme.Modules.pushforward g).obj N) (x : (relativeGlobalSections f).obj P) :
    scalarSectionsBaseChangeMapOf φ f f' g w a ((1 : T) ⊗ₜ[R,φ.hom] x) = a.app ⊤ x := by
  have h := congrArg (fun k => k x) (scalarSectionsBaseChangeMapOf_homEquiv φ f f' g w a)
  simpa only [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
    sectionsBaseChangeMapOf_apply] using h

/-- The `Spec.map φ`-adjoint of the comparison is the ordinary sections map on top sections. -/
lemma pushforwardBaseChangeOf_adjoint_app_top {P : X.Modules} {N : X'.Modules}
    (a : P ⟶ (Scheme.Modules.pushforward g).obj N) (m : (relativeGlobalSections f).obj P) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _
      (pushforwardBaseChangeOf f (Spec.map φ) f' g w a)).app ⊤ m =
      sectionsBaseChangeMapOf φ f f' g w a m := by
  simp only [pushforwardBaseChangeOf_homEquiv, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, ConcreteCategory.comp_apply,
    sectionsBaseChangeMapOf_apply]
  exact pushforwardSquareIso_hom_app_top φ f f' g w _ _

/-- The affine sheaf comparison agrees with the scalar comparison on the canonical global
generators. -/
@[reassoc]
theorem pullback_fromTildeΓ_comp_pushforwardBaseChangeOf {P : X.Modules} {N : X'.Modules}
    (a : P ⟶ (Scheme.Modules.pushforward g).obj N) :
    (Scheme.Modules.pullback (Spec.map φ)).map
        ((Scheme.Modules.pushforward f).obj P).fromTildeΓ ≫
      pushforwardBaseChangeOf f (Spec.map φ) f' g w a =
    (tildePullbackIso φ ((relativeGlobalSections f).obj P)).hom ≫
      affineDirectImageTildeMapOf φ f f' g w a := by
  dsimp only [relativeGlobalSections, Functor.comp_obj]
  apply tildePullback_hom_ext
  intro m
  rw [tildePullbackAdjoint, Adjunction.homEquiv_naturality_left,
    tildePullbackAdjoint, Adjunction.homEquiv_naturality_right]
  change ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _
      (pushforwardBaseChangeOf f (Spec.map φ) f' g w a)).app ⊤
        (((Scheme.Modules.pushforward f).obj P).fromTildeΓ.app ⊤
          (tilde.toOpen ((moduleSpecΓFunctor (R := R)).obj
            ((Scheme.Modules.pushforward f).obj P)) ⊤ m)) =
    (affineDirectImageTildeMapOf φ f f' g w a).app ⊤
      ((tildePullbackAdjoint φ
        (tildePullbackIso φ ((moduleSpecΓFunctor (R := R)).obj
          ((Scheme.Modules.pushforward f).obj P))).hom).app ⊤
          (tilde.toOpen ((moduleSpecΓFunctor (R := R)).obj
            ((Scheme.Modules.pushforward f).obj P)) ⊤ m))
  have hc (Q : (Spec R).Modules) (x : (moduleSpecΓFunctor (R := R)).obj Q) :
      Q.fromTildeΓ.app ⊤ (tilde.toOpen ((moduleSpecΓFunctor (R := R)).obj Q) ⊤ x) = x := by
    have h := ConcreteCategory.congr_hom (Scheme.Modules.toOpen_fromTildeΓ_app Q ⊤) x
    change Q.fromTildeΓ.app ⊤
      (tilde.toOpen ((moduleSpecΓFunctor (R := R)).obj Q) ⊤ x) =
        Q.presheaf.map (homOfLE (le_refl ⊤)).op x at h
    simpa using h
  rw [hc, pushforwardBaseChangeOf_adjoint_app_top,
    tildePullbackIso_adjoint_toOpen_top]
  unfold affineDirectImageTildeMapOf
  change sectionsBaseChangeMapOf φ f f' g w a m =
    ((Scheme.Modules.pushforward f').obj N).fromTildeΓ.app ⊤
      ((tilde.map (scalarSectionsBaseChangeMapOf φ f f' g w a)).app ⊤
        (tilde.toOpen _ ⊤ ((1 : T) ⊗ₜ[R,φ.hom] m)))
  have hm := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (scalarSectionsBaseChangeMapOf φ f f' g w a) ⊤)
      ((1 : T) ⊗ₜ[R,φ.hom] m)
  change (tilde.map (scalarSectionsBaseChangeMapOf φ f f' g w a)).app ⊤
      (tilde.toOpen _ ⊤ ((1 : T) ⊗ₜ[R,φ.hom] m)) =
    tilde.toOpen _ ⊤
      ((scalarSectionsBaseChangeMapOf φ f f' g w a) ((1 : T) ⊗ₜ[R,φ.hom] m)) at hm
  dsimp only [relativeGlobalSections, Functor.comp_obj] at *
  rw [hm]
  have hcT (Q : (Spec T).Modules) (x : (moduleSpecΓFunctor (R := T)).obj Q) :
      Q.fromTildeΓ.app ⊤ (tilde.toOpen ((moduleSpecΓFunctor (R := T)).obj Q) ⊤ x) = x := by
    have h := ConcreteCategory.congr_hom (Scheme.Modules.toOpen_fromTildeΓ_app Q ⊤) x
    change Q.fromTildeΓ.app ⊤
      (tilde.toOpen ((moduleSpecΓFunctor (R := T)).obj Q) ⊤ x) =
        Q.presheaf.map (homOfLE (le_refl ⊤)).op x at h
    simpa using h
  rw [hcT]
  exact (scalarSectionsBaseChangeMapOf_one_tmul φ f f' g w a m).symm

end Spectra

end Langlands.AlgebraicGeometry.Modules.DerivedSections
