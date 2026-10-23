import Langlands.AbelianScheme.Lie
import Langlands.AlgebraicGeometry.RelativeDifferentialsMapsCoherence

/-! # Functoriality of relative Lie modules -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S : AlgebraicGeometry.Scheme.{u}}

private def sectionPullbackIso {X Y : AlgebraicGeometry.Scheme.{u}}
    (eX : S ⟶ X) (eY : S ⟶ Y) (f : X ⟶ Y) (w : eX ≫ f = eY) :
    pullback eY ≅ pullback f ⋙ pullback eX :=
  (pullbackCongr w).symm ≪≫ (pullbackComp eX f).symm

private lemma sectionPullbackIso_comp {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (eX : S ⟶ X) (eY : S ⟶ Y) (eZ : S ⟶ Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (wf : eX ≫ f = eY) (wg : eY ≫ g = eZ) (M : Z.Modules) :
    (sectionPullbackIso eY eZ g wg).hom.app M ≫
        (sectionPullbackIso eX eY f wf).hom.app ((pullback g).obj M) =
      (sectionPullbackIso eX eZ (f ≫ g) (by rw [← Category.assoc, wf, wg])).hom.app M ≫
        (pullback eX).map ((pullbackComp f g).inv.app M) := by
  subst eY
  subst eZ
  have h := NatTrans.congr_app (pseudofunctor_associativity eX f g) M
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app] at h
  erw [Category.id_comp (obj := S.Modules)] at h
  apply (cancel_mono ((pullbackComp eX f).hom.app ((pullback g).obj M) ≫
    (pullbackComp (eX ≫ f) g).hom.app M)).1
  simp only [sectionPullbackIso, Iso.trans_hom, Iso.symm_hom,
    pullbackCongr, eqToIso.inv, eqToHom_refl, Category.id_comp,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [h]
  rw [Iso.inv_hom_id_app]
  rfl

/-- The pullback comparison arising from preservation of the identity section. -/
def identityPullbackIso {G H : GroupScheme S} (f : G ⟶ H) :
    pullback H.identitySection ≅ pullback f.hom.hom.left ⋙ pullback G.identitySection :=
  sectionPullbackIso G.identitySection H.identitySection f.hom.hom.left
    (identitySection_naturality f)

lemma identityPullbackIso_comp {G H I : GroupScheme S} (f : G ⟶ H) (g : H ⟶ I)
    (M : I.X.left.Modules) :
    (identityPullbackIso g).hom.app M ≫
        (identityPullbackIso f).hom.app ((pullback g.hom.hom.left).obj M) =
      (identityPullbackIso (f ≫ g)).hom.app M ≫
        (pullback G.identitySection).map
          ((pullbackComp f.hom.hom.left g.hom.hom.left).inv.app M) :=
  sectionPullbackIso_comp _ _ _ _ _ _ _ _

/-- The actual contravariant differential on cotangent modules at the identity. -/
def cotangentMap {G H : GroupScheme S} (f : G ⟶ H) :
    H.cotangentAtIdentity ⟶ G.cotangentAtIdentity :=
  (identityPullbackIso f).hom.app (Langlands.Scheme.relativeDifferentials H.X.hom) ≫
    (pullback G.identitySection).map
      (Langlands.Scheme.relativeDifferentialsMap f.hom.hom.left f.hom.hom.w)

@[simp]
lemma cotangentMap_id (G : GroupScheme S) : cotangentMap (𝟙 G) = 𝟙 G.cotangentAtIdentity := by
  change ((pullbackCongr (Category.comp_id G.identitySection)).inv.app _ ≫
    (pullbackComp G.identitySection (𝟙 G.X.left)).inv.app _) ≫
    (pullback G.identitySection).map
      (Langlands.Scheme.relativeDifferentialsMap (𝟙 G.X.left) (Category.id_comp G.X.hom)) =
        𝟙 ((pullback G.identitySection).obj (Langlands.Scheme.relativeDifferentials G.X.hom))
  rw [Langlands.Scheme.relativeDifferentialsMap_id]
  have h :
      (pullbackComp G.identitySection (𝟙 G.X.left)).inv.app
          (Langlands.Scheme.relativeDifferentials G.X.hom) ≫
        (pullback G.identitySection).map
          ((pullbackId G.X.left).hom.app (Langlands.Scheme.relativeDifferentials G.X.hom)) ≫
        𝟙 ((pullback G.identitySection).obj (Langlands.Scheme.relativeDifferentials G.X.hom)) =
      eqToHom (by simp) :=
    NatTrans.congr_app (pseudofunctor_left_unitality G.identitySection)
      (Langlands.Scheme.relativeDifferentials G.X.hom)
  erw [Category.comp_id (obj := S.Modules)] at h
  rw [Category.assoc, h]
  simp only [pullbackCongr, eqToIso.inv, eqToHom_refl]
  rfl

lemma cotangentMap_comp {G H I : GroupScheme S} (f : G ⟶ H) (g : H ⟶ I) :
    cotangentMap (f ≫ g) = cotangentMap g ≫ cotangentMap f := by
  dsimp only [cotangentMap]
  change (identityPullbackIso (f ≫ g)).hom.app _ ≫
    (pullback G.identitySection).map
      (Langlands.Scheme.relativeDifferentialsMap (f.hom.hom.left ≫ g.hom.hom.left)
        (by rw [Category.assoc, g.hom.hom.w, f.hom.hom.w])) = _
  rw [← Langlands.Scheme.relativeDifferentialsMap_comp
    f.hom.hom.left g.hom.hom.left f.hom.hom.w g.hom.hom.w]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (identityPullbackIso_comp f g
    (Langlands.Scheme.relativeDifferentials I.X.hom))]
  have hn := (identityPullbackIso f).hom.naturality
    (Langlands.Scheme.relativeDifferentialsMap g.hom.hom.left g.hom.hom.w)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]

/-- The differential on Lie modules, obtained by dualizing the cotangent map. -/
def lieMap {G H : GroupScheme S} (f : G ⟶ H) : G.Lie ⟶ H.Lie :=
  Langlands.Scheme.Modules.dualMap (cotangentMap f)

/-- The Lie differential acts on a local functional by precomposition with the
cotangent differential. -/
lemma lieMap_eval {G H : GroupScheme S} (f : G ⟶ H) (U : S.Opens)
    (v : Γ(G.Lie, U)) (ω : Γ(H.cotangentAtIdentity, U)) :
    H.lieEval U ((lieMap f).app U v) ω =
      G.lieEval U v ((cotangentMap f).app U ω) :=
  Langlands.Scheme.Modules.dualMap_eval (cotangentMap f) U v ω

@[simp]
lemma lieMap_id (G : GroupScheme S) : lieMap (𝟙 G) = 𝟙 G.Lie := by
  simp [lieMap, Lie]

@[simp]
lemma lieMap_comp {G H I : GroupScheme S} (f : G ⟶ H) (g : H ⟶ I) :
    lieMap (f ≫ g) = lieMap f ≫ lieMap g := by
  simp [lieMap, cotangentMap_comp]

/-- The relative Lie module as a covariant functor on actual group schemes. -/
def lieFunctor (S : AlgebraicGeometry.Scheme.{u}) : GroupScheme S ⥤ S.Modules where
  obj G := G.Lie
  map f := lieMap f
  map_id G := lieMap_id G
  map_comp f g := lieMap_comp f g

end Langlands.GroupScheme

namespace Langlands.CommGroupScheme

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- The relative Lie differential of a commutative-group-scheme homomorphism. -/
abbrev lieMap {G H : CommGroupScheme S} (f : G ⟶ H) : G.Lie ⟶ H.Lie :=
  GroupScheme.lieMap (groupHom f)

@[simp]
lemma lieMap_id (G : CommGroupScheme S) : lieMap (𝟙 G) = 𝟙 G.Lie :=
  GroupScheme.lieMap_id G.toGrp

@[simp]
lemma lieMap_comp {G H I : CommGroupScheme S} (f : G ⟶ H) (g : H ⟶ I) :
    lieMap (f ≫ g) = lieMap f ≫ lieMap g :=
  GroupScheme.lieMap_comp (groupHom f) (groupHom g)

/-- The relative Lie functor on commutative group schemes. -/
def lieFunctor (S : AlgebraicGeometry.Scheme.{u}) : CommGroupScheme S ⥤ S.Modules where
  obj G := G.Lie
  map f := lieMap f
  map_id G := lieMap_id G
  map_comp f g := lieMap_comp f g

end Langlands.CommGroupScheme

namespace Langlands.AbelianScheme

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- The relative Lie differential of an abelian-scheme homomorphism. -/
abbrev lieMap {A B : AbelianScheme S} (f : A ⟶ B) : A.Lie ⟶ B.Lie :=
  GroupScheme.lieMap (groupHom f)

@[simp]
lemma lieMap_id (A : AbelianScheme S) : lieMap (𝟙 A) = 𝟙 A.Lie :=
  GroupScheme.lieMap_id A.toGrp

@[simp]
lemma lieMap_comp {A B C : AbelianScheme S} (f : A ⟶ B) (g : B ⟶ C) :
    lieMap (f ≫ g) = lieMap f ≫ lieMap g :=
  GroupScheme.lieMap_comp (groupHom f) (groupHom g)

/-- The relative Lie functor on abelian schemes over the fixed base. -/
def lieFunctor (S : AlgebraicGeometry.Scheme.{u}) : AbelianScheme S ⥤ S.Modules where
  obj A := A.Lie
  map f := lieMap f
  map_id A := lieMap_id A
  map_comp f g := lieMap_comp f g

end Langlands.AbelianScheme
