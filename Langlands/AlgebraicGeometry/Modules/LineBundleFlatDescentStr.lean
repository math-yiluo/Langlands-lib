import Langlands.AlgebraicGeometry.Modules.LineBundleIsoDescentProof
import Langlands.AlgebraicGeometry.Modules.PullbackTransport
import Langlands.AlgebraicGeometry.Modules.CommonSourceTransitionTransport

/-! # Descent structures for effective flat descent of line bundles -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule
open Langlands.SchemeModule.RigidifiedModule

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.Scheme.Modules.LineBundleFlatDescent

section Transport

variable {Z Z' A B : Scheme.{u}}

/-- The comparison `k^* (u^* C) ≅ u'^* C` for `k ≫ u = u'` is Mathlib's composition
comparison when `u' = k ≫ u`. -/
lemma compIso_rfl (k : Z' ⟶ Z) (u : Z ⟶ A) (C : A.Modules) :
    compIso k u (k ≫ u) rfl C = (Scheme.Modules.pullbackComp k u).app C := by
  ext1
  rw [compIso_hom, compHom_rfl]
  rfl

/-- Associativity of the composition comparisons. -/
@[reassoc]
lemma compIso_assoc {W : Scheme.{u}} (k : Z' ⟶ Z) (g : Z ⟶ A) (c : A ⟶ W) (g' : Z' ⟶ A)
    (w : Z ⟶ W) (w' : Z' ⟶ W) (hg : k ≫ g = g') (hw : g ≫ c = w) (hw' : k ≫ w = w')
    (hgw : g' ≫ c = w') (C : W.Modules) :
    (compIso k g g' hg ((Scheme.Modules.pullback c).obj C)).hom ≫ (compIso g' c w' hgw C).hom =
      (Scheme.Modules.pullback k).map (compIso g c w hw C).hom ≫ (compIso k w w' hw' C).hom := by
  simp only [compIso_hom]
  exact compHom_assoc k g c g' w w' hg hw hgw hw' C

/-- Composition comparisons are natural in the module. -/
@[reassoc]
lemma compIso_naturality (k : Z' ⟶ Z) (u : Z ⟶ A) (u' : Z' ⟶ A) (hu : k ≫ u = u')
    {C C' : A.Modules} (φ : C ⟶ C') :
    (Scheme.Modules.pullback k).map ((Scheme.Modules.pullback u).map φ) ≫
        (compIso k u u' hu C').hom =
      (compIso k u u' hu C).hom ≫ (Scheme.Modules.pullback u').map φ := by
  subst hu
  rw [compIso_rfl, compIso_rfl]
  exact (Scheme.Modules.pullbackComp k u).hom.naturality φ

/-- Transport of a morphism `u^* C ⟶ v^* D` between pullbacks of modules on two bases
along `k`, identified with pullbacks along prescribed composites. -/
def tr (k : Z' ⟶ Z) {C : A.Modules} {D : B.Modules} {u : Z ⟶ A} {v : Z ⟶ B}
    {u' : Z' ⟶ A} {v' : Z' ⟶ B} (hu : k ≫ u = u') (hv : k ≫ v = v')
    (φ : (Scheme.Modules.pullback u).obj C ⟶ (Scheme.Modules.pullback v).obj D) :
    (Scheme.Modules.pullback u').obj C ⟶ (Scheme.Modules.pullback v').obj D :=
  (compIso k u u' hu C).inv ≫ (Scheme.Modules.pullback k).map φ ≫ (compIso k v v' hv D).hom

variable (k : Z' ⟶ Z)

@[reassoc]
lemma tr_comp {E : Scheme.{u}} {C : A.Modules} {D : B.Modules} {G : E.Modules}
    {u : Z ⟶ A} {v : Z ⟶ B} {w : Z ⟶ E} {u' : Z' ⟶ A} {v' : Z' ⟶ B} {w' : Z' ⟶ E}
    (hu : k ≫ u = u') (hv : k ≫ v = v') (hw : k ≫ w = w')
    (φ : (Scheme.Modules.pullback u).obj C ⟶ (Scheme.Modules.pullback v).obj D)
    (ψ : (Scheme.Modules.pullback v).obj D ⟶ (Scheme.Modules.pullback w).obj G) :
    tr k hu hw (φ ≫ ψ) = tr k hu hv φ ≫ tr k hv hw ψ := by
  simp [tr]

@[simp]
lemma tr_id {C : A.Modules} {u : Z ⟶ A} {u' : Z' ⟶ A} (hu : k ≫ u = u') :
    tr k hu hu (𝟙 ((Scheme.Modules.pullback u).obj C)) = 𝟙 _ := by
  simp [tr]

/-- Transport of the pullback of a module morphism. -/
lemma tr_map {C C' : A.Modules} {u : Z ⟶ A} {u' : Z' ⟶ A} (hu : k ≫ u = u') (φ : C ⟶ C') :
    tr k hu hu ((Scheme.Modules.pullback u).map φ) = (Scheme.Modules.pullback u').map φ := by
  unfold tr
  rw [compIso_naturality, Iso.inv_hom_id_assoc]

/-- Transport of a composition comparison is a composition comparison. -/
lemma tr_compIso {W : Scheme.{u}} (g : Z ⟶ A) (c : A ⟶ W) (w : Z ⟶ W) (hw : g ≫ c = w)
    (g' : Z' ⟶ A) (w' : Z' ⟶ W) (hg : k ≫ g = g') (hw' : k ≫ w = w') (hgw : g' ≫ c = w')
    (C : W.Modules) :
    tr k hg hw' (compIso g c w hw C).hom = (compIso g' c w' hgw C).hom := by
  unfold tr
  rw [← compIso_assoc k g c g' w w' hg hw hw' hgw C, Iso.inv_hom_id_assoc]

/-- Transport of the inverse of an isomorphism. -/
lemma tr_inv {C : A.Modules} {D : B.Modules} {u : Z ⟶ A} {v : Z ⟶ B}
    {u' : Z' ⟶ A} {v' : Z' ⟶ B} (hu : k ≫ u = u') (hv : k ≫ v = v')
    (φ : (Scheme.Modules.pullback u).obj C ≅ (Scheme.Modules.pullback v).obj D) :
    tr k hu hv φ.hom ≫ tr k hv hu φ.inv = 𝟙 _ := by
  rw [← tr_comp, Iso.hom_inv_id, tr_id]

lemma tr_inv' {C : A.Modules} {D : B.Modules} {u : Z ⟶ A} {v : Z ⟶ B}
    {u' : Z' ⟶ A} {v' : Z' ⟶ B} (hu : k ≫ u = u') (hv : k ≫ v = v')
    (φ : (Scheme.Modules.pullback u).obj C ≅ (Scheme.Modules.pullback v).obj D) :
    tr k hv hu φ.inv ≫ tr k hu hv φ.hom = 𝟙 _ := by
  rw [← tr_comp, Iso.inv_hom_id, tr_id]

/-- If an isomorphism is the transport of another, so is its inverse. -/
lemma inv_eq_tr {C : A.Modules} {D : B.Modules} {u : Z ⟶ A} {v : Z ⟶ B}
    {u' : Z' ⟶ A} {v' : Z' ⟶ B} (hu : k ≫ u = u') (hv : k ≫ v = v')
    (φ : (Scheme.Modules.pullback u).obj C ≅ (Scheme.Modules.pullback v).obj D)
    (ψ : (Scheme.Modules.pullback u').obj C ≅ (Scheme.Modules.pullback v').obj D)
    (h : ψ.hom = tr k hu hv φ.hom) : ψ.inv = tr k hv hu φ.inv := by
  rw [← cancel_epi ψ.hom, Iso.hom_inv_id, h, tr_inv]

/-- Transport of the inverse of a composition comparison. -/
lemma tr_compIso_inv {W : Scheme.{u}} (g : Z ⟶ A) (c : A ⟶ W) (w : Z ⟶ W) (hw : g ≫ c = w)
    (g' : Z' ⟶ A) (w' : Z' ⟶ W) (hg : k ≫ g = g') (hw' : k ≫ w = w') (hgw : g' ≫ c = w')
    (C : W.Modules) :
    tr k hw' hg (compIso g c w hw C).inv = (compIso g' c w' hgw C).inv :=
  (inv_eq_tr k hg hw' (compIso g c w hw C) (compIso g' c w' hgw C)
    (tr_compIso k g c w hw g' w' hg hw' hgw C).symm).symm

/-- The existing isomorphism transport has the morphism transport as its forward map. -/
@[simp]
lemma transport_hom {C : A.Modules} {D : B.Modules} {u : Z ⟶ A} {v : Z ⟶ B}
    {u' : Z' ⟶ A} {v' : Z' ⟶ B} (hu : k ≫ u = u') (hv : k ≫ v = v')
    (φ : (Scheme.Modules.pullback u).obj C ≅ (Scheme.Modules.pullback v).obj D) :
    (CommonSourceCocycle.transport k u v u' v' hu hv φ).hom = tr k hu hv φ.hom :=
  rfl

/-- Transport along a composite is iterated transport. -/
lemma tr_tr {W : Scheme.{u}} (k' : W ⟶ Z') {C : A.Modules} {D : B.Modules}
    {u : Z ⟶ A} {v : Z ⟶ B} {u' : Z' ⟶ A} {v' : Z' ⟶ B} {u'' : W ⟶ A} {v'' : W ⟶ B}
    (hu : k ≫ u = u') (hv : k ≫ v = v') (hu' : k' ≫ u' = u'') (hv' : k' ≫ v' = v'')
    (hu'' : (k' ≫ k) ≫ u = u'') (hv'' : (k' ≫ k) ≫ v = v'')
    (φ : (Scheme.Modules.pullback u).obj C ⟶ (Scheme.Modules.pullback v).obj D) :
    tr k' hu' hv' (tr k hu hv φ) = tr (k' ≫ k) hu'' hv'' φ := by
  have eC := compIso_assoc k' k u (k' ≫ k) u' u'' rfl hu hu' hu'' C
  have eD := compIso_assoc k' k v (k' ≫ k) v' v'' rfl hv hv' hv'' D
  rw [compIso_rfl] at eC eD
  simp only [Iso.app_hom] at eC eD
  have eC' : (compIso k' u' u'' hu' C).inv ≫
      (Scheme.Modules.pullback k').map (compIso k u u' hu C).inv =
        (compIso (k' ≫ k) u u'' hu'' C).inv ≫
          (Scheme.Modules.pullbackComp k' k).inv.app ((Scheme.Modules.pullback u).obj C) := by
    rw [← cancel_mono ((Scheme.Modules.pullback k').map (compIso k u u' hu C).hom),
      ← cancel_mono (compIso k' u' u'' hu' C).hom]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← eC]
    simp
  have nat := (Scheme.Modules.pullbackComp k' k).hom.naturality φ
  simp only [Functor.comp_map] at nat
  unfold tr
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% eC', ← eD, reassoc_of% nat]
  simp

/-- Iterated transport along a composite equal to a prescribed map. -/
lemma tr_tr_eq {W : Scheme.{u}} (k' : W ⟶ Z') {m : W ⟶ Z} (hm : k' ≫ k = m)
    {C : A.Modules} {D : B.Modules}
    {u : Z ⟶ A} {v : Z ⟶ B} {u' : Z' ⟶ A} {v' : Z' ⟶ B} {u'' : W ⟶ A} {v'' : W ⟶ B}
    (hu : k ≫ u = u') (hv : k ≫ v = v') (hu' : k' ≫ u' = u'') (hv' : k' ≫ v' = v'')
    (hu'' : m ≫ u = u'') (hv'' : m ≫ v = v'')
    (φ : (Scheme.Modules.pullback u).obj C ⟶ (Scheme.Modules.pullback v).obj D) :
    tr k' hu' hv' (tr k hu hv φ) = tr m hu'' hv'' φ := by
  subst hm
  exact tr_tr k k' hu hv hu' hv' hu'' hv'' φ

lemma tr_congr {k' : Z' ⟶ Z} (e : k = k') {C : A.Modules} {D : B.Modules}
    {u : Z ⟶ A} {v : Z ⟶ B} {u' : Z' ⟶ A} {v' : Z' ⟶ B}
    (hu : k ≫ u = u') (hv : k ≫ v = v') (hu' : k' ≫ u = u') (hv' : k' ≫ v = v')
    (φ : (Scheme.Modules.pullback u).obj C ⟶ (Scheme.Modules.pullback v).obj D) :
    tr k hu hv φ = tr k' hu' hv' φ := by
  subst e
  rfl

/-- Transport is injective on morphisms whose pullbacks along `k` differ. -/
lemma map_eq_of_tr_eq {C : A.Modules} {D : B.Modules} {u : Z ⟶ A} {v : Z ⟶ B}
    {u' : Z' ⟶ A} {v' : Z' ⟶ B} (hu : k ≫ u = u') (hv : k ≫ v = v')
    (φ ψ : (Scheme.Modules.pullback u).obj C ⟶ (Scheme.Modules.pullback v).obj D)
    (h : tr k hu hv φ = tr k hu hv ψ) :
    (Scheme.Modules.pullback k).map φ = (Scheme.Modules.pullback k).map ψ := by
  unfold tr at h
  rwa [cancel_epi, cancel_mono] at h

end Transport

section EqualComposite

variable {U A B : Scheme.{u}} (q : A ⟶ B)

/-- The canonical equal-composite comparison through a common composite. -/
lemma equalCompositeIso_hom_eq_compIso (a b : U ⟶ A) (h : a ≫ q = b ≫ q) (w : U ⟶ B)
    (ha : a ≫ q = w) (hb : b ≫ q = w) (M : B.Modules) :
    (equalCompositeIso q a b h M).hom = (compIso a q w ha M).hom ≫ (compIso b q w hb M).inv := by
  subst hb
  rw [equalCompositeIso_hom_eq_compHom, ← compIso_hom, compIso_rfl]
  rfl

/-- Compatibility of a morphism with the equal-composite comparisons follows from equality
of its transports to a common composite. -/
lemma compat_of_tr_eq {M₁ M₂ : B.Modules}
    (f : (Scheme.Modules.pullback q).obj M₁ ⟶ (Scheme.Modules.pullback q).obj M₂)
    (a b : U ⟶ A) (h : a ≫ q = b ≫ q) (w : U ⟶ B) (ha : a ≫ q = w) (hb : b ≫ q = w)
    (H : tr a ha ha f = tr b hb hb f) :
    (Scheme.Modules.pullback a).map f ≫ (equalCompositeIso q a b h M₂).hom =
      (equalCompositeIso q a b h M₁).hom ≫ (Scheme.Modules.pullback b).map f := by
  rw [equalCompositeIso_hom_eq_compIso q a b h w ha hb,
    equalCompositeIso_hom_eq_compIso q a b h w ha hb]
  unfold tr at H
  rw [← cancel_epi (compIso a q w ha M₁).inv, ← cancel_mono (compIso b q w hb M₂).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  exact H

end EqualComposite

section Faithful

/-- Pullback along a quasi-compact faithfully flat morphism is faithful on isomorphisms of
line bundles. -/
lemma iso_ext_of_pullback {A B : Scheme.{u}} (q : A ⟶ B) [QuasiCompact q] [Flat q]
    [Surjective q] {M N : B.Modules} (hM : IsLocallyFreeRankOne M)
    (hN : IsLocallyFreeRankOne N) (φ ψ : M ≅ N)
    (h : (Scheme.Modules.pullback q).map φ.hom = (Scheme.Modules.pullback q).map ψ.hom) :
    φ = ψ := by
  obtain ⟨e₀, -, he₀⟩ := LineBundleIsoDescent.lineBundleIsoDescent A B q inferInstance
    inferInstance inferInstance M N hM hN ((Scheme.Modules.pullback q).mapIso φ)
    (fun U a b hab ↦ equalCompositeIso_hom_naturality q a b hab φ.hom)
  have h₁ := he₀ φ rfl
  have h₂ := he₀ ψ (Iso.ext h.symm)
  exact h₁.trans h₂.symm

/-- Transport along a quasi-compact faithfully flat morphism is faithful on isomorphisms of
line bundles. -/
lemma iso_ext_of_tr {Z Z' A B : Scheme.{u}} (k : Z' ⟶ Z) [QuasiCompact k] [Flat k]
    [Surjective k] {C : A.Modules} {D : B.Modules} {u : Z ⟶ A} {v : Z ⟶ B}
    (hC : IsLocallyFreeRankOne ((Scheme.Modules.pullback u).obj C))
    (hD : IsLocallyFreeRankOne ((Scheme.Modules.pullback v).obj D))
    {u' : Z' ⟶ A} {v' : Z' ⟶ B} (hu : k ≫ u = u') (hv : k ≫ v = v')
    (φ ψ : (Scheme.Modules.pullback u).obj C ≅ (Scheme.Modules.pullback v).obj D)
    (h : tr k hu hv φ.hom = tr k hu hv ψ.hom) : φ = ψ :=
  iso_ext_of_pullback k hC hD φ ψ (map_eq_of_tr_eq k hu hv _ _ h)

end Faithful

section Datum

variable {X Y : Scheme.{u}} (p : X ⟶ Y) (F : X.Modules)

/-- Descent data for a module along `p`, in equal-composite form: isomorphisms on all pairs of
maps with equal composites, natural under precomposition and satisfying the cocycle law. -/
structure Datum where
  /-- The descent isomorphism attached to a pair of maps with equal composites. -/
  θ : ∀ (U : Scheme.{u}) (a b : U ⟶ X), a ≫ p = b ≫ p →
    ((Scheme.Modules.pullback a).obj F ≅ (Scheme.Modules.pullback b).obj F)
  /-- Naturality under precomposition. -/
  nat : ∀ (U V : Scheme.{u}) (k : V ⟶ U) (a b : U ⟶ X) (h : a ≫ p = b ≫ p)
      (h' : (k ≫ a) ≫ p = (k ≫ b) ≫ p),
    (θ V (k ≫ a) (k ≫ b) h').hom =
      (Scheme.Modules.pullbackComp k a).inv.app F ≫
        (Scheme.Modules.pullback k).map (θ U a b h).hom ≫
          (Scheme.Modules.pullbackComp k b).hom.app F
  /-- The cocycle law. -/
  coc : ∀ (U : Scheme.{u}) (a b c : U ⟶ X) (h : a ≫ p = b ≫ p) (h' : b ≫ p = c ≫ p)
      (h'' : a ≫ p = c ≫ p),
    (θ U a b h).hom ≫ (θ U b c h').hom = (θ U a c h'').hom

variable {p F} (D : Datum p F)

namespace Datum

/-- Naturality of the descent isomorphisms, in transport form. -/
lemma θ_tr {U V : Scheme.{u}} (k : V ⟶ U) {a b : U ⟶ X} {a' b' : V ⟶ X} (ha : k ≫ a = a')
    (hb : k ≫ b = b') (h : a ≫ p = b ≫ p) (h' : a' ≫ p = b' ≫ p) :
    (D.θ V a' b' h').hom = tr k ha hb (D.θ U a b h).hom := by
  subst ha hb
  rw [D.nat U V k a b h h']
  unfold tr
  rw [compIso_rfl, compIso_rfl]
  simp

/-- The descent isomorphism of a pair of equal maps is the identity. -/
@[simp]
lemma θ_self {U : Scheme.{u}} (a : U ⟶ X) (h : a ≫ p = a ≫ p) : (D.θ U a a h).hom = 𝟙 _ := by
  rw [← cancel_epi (D.θ U a a h).hom, D.coc U a a a h h h, Category.comp_id]

/-- The descent isomorphisms are symmetric. -/
lemma θ_symm {U : Scheme.{u}} (a b : U ⟶ X) (h : a ≫ p = b ≫ p) (h' : b ≫ p = a ≫ p) :
    (D.θ U b a h').hom = (D.θ U a b h).inv := by
  rw [← cancel_epi (D.θ U a b h).hom, D.coc U a b a h h' rfl, θ_self, Iso.hom_inv_id]

end Datum

end Datum

section Str

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {F : X.Modules} (D : Datum p F)

/-- A descended module over `t : T ⟶ Y`: a module `N` on `T` with isomorphisms
`h^* N ≅ g^* F` for all `h ≫ t = g ≫ p`, natural under precomposition and compatible with
the descent data. -/
structure Str {T : Scheme.{u}} (t : T ⟶ Y) (N : T.Modules) where
  /-- The comparison isomorphisms. -/
  γ : ∀ (Z : Scheme.{u}) (g : Z ⟶ X) (h : Z ⟶ T), h ≫ t = g ≫ p →
    ((Scheme.Modules.pullback h).obj N ≅ (Scheme.Modules.pullback g).obj F)
  /-- Naturality under precomposition. -/
  nat : ∀ (Z Z' : Scheme.{u}) (k : Z' ⟶ Z) (g : Z ⟶ X) (h : Z ⟶ T) (hs : h ≫ t = g ≫ p)
      (g' : Z' ⟶ X) (h' : Z' ⟶ T) (hs' : h' ≫ t = g' ≫ p) (hg : k ≫ g = g')
      (hh : k ≫ h = h'),
    (γ Z' g' h' hs').hom = tr k hh hg (γ Z g h hs).hom
  /-- Compatibility with the descent data. -/
  coc : ∀ (Z : Scheme.{u}) (g₁ g₂ : Z ⟶ X) (h : Z ⟶ T) (hs₁ : h ≫ t = g₁ ≫ p)
      (hs₂ : h ≫ t = g₂ ≫ p) (hθ : g₁ ≫ p = g₂ ≫ p),
    (γ Z g₁ h hs₁).hom ≫ (D.θ Z g₁ g₂ hθ).hom = (γ Z g₂ h hs₂).hom

variable {D}

namespace Str

variable {T : Scheme.{u}}

/-- A morphism of modules compatible with two descended structures. The two base maps are
allowed to differ syntactically. -/
def Hom {t t' : T ⟶ Y} {N N' : T.Modules} (S : Str D t N) (S' : Str D t' N') (φ : N ⟶ N') :
    Prop :=
  ∀ (Z : Scheme.{u}) (g : Z ⟶ X) (h : Z ⟶ T) (hs : h ≫ t = g ≫ p) (hs' : h ≫ t' = g ≫ p),
    (Scheme.Modules.pullback h).map φ ≫ (S'.γ Z g h hs').hom = (S.γ Z g h hs).hom

lemma Hom.id {t : T ⟶ Y} {N : T.Modules} (S : Str D t N) : Hom S S (𝟙 N) := by
  intro Z g h hs hs'
  simp

lemma Hom.comp {t t' t'' : T ⟶ Y} (ht : t = t') {N N' N'' : T.Modules} {S : Str D t N}
    {S' : Str D t' N'} {S'' : Str D t'' N''} {φ : N ⟶ N'} {ψ : N' ⟶ N''} (hφ : Hom S S' φ)
    (hψ : Hom S' S'' ψ) : Hom S S'' (φ ≫ ψ) := by
  intro Z g h hs hs''
  have hs' : h ≫ t' = g ≫ p := ht ▸ hs
  rw [Functor.map_comp, Category.assoc, hψ Z g h hs' hs'', hφ Z g h hs hs']

lemma Hom.inv {t t' : T ⟶ Y} {N N' : T.Modules} {S : Str D t N}
    {S' : Str D t' N'} {φ : N ≅ N'} (hφ : Hom S S' φ.hom) : Hom S' S φ.inv := by
  intro Z g h hs' hs
  rw [← hφ Z g h hs hs', ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Restriction of a descended structure along `u : T' ⟶ T`. -/
def restrict {t : T ⟶ Y} {N : T.Modules} (S : Str D t N) {T' : Scheme.{u}} (u : T' ⟶ T)
    (t' : T' ⟶ Y) (hu : u ≫ t = t') : Str D t' ((Scheme.Modules.pullback u).obj N) where
  γ Z g h hs := compIso h u (h ≫ u) rfl N ≪≫
    S.γ Z g (h ≫ u) (by rw [Category.assoc, hu, hs])
  nat Z Z' k g h hs g' h' hs' hg hh := by
    have hk : k ≫ (h ≫ u) = h' ≫ u := by rw [← Category.assoc, hh]
    rw [Iso.trans_hom, Iso.trans_hom, tr_comp k hh hk hg, tr_compIso k h u (h ≫ u) rfl h' (h' ≫ u) hh hk rfl,
      ← S.nat Z Z' k g (h ≫ u) _ g' (h' ≫ u) _ hg hk]
  coc Z g₁ g₂ h hs₁ hs₂ hθ := by
    simp only [Iso.trans_hom, Category.assoc]
    rw [S.coc]

/-- The comparison isomorphisms of a restriction, with a prescribed composite. -/
lemma restrict_γ {t : T ⟶ Y} {N : T.Modules} (S : Str D t N) {T' : Scheme.{u}} (u : T' ⟶ T)
    (t' : T' ⟶ Y) (hu : u ≫ t = t') {Z : Scheme.{u}} (g : Z ⟶ X) (h : Z ⟶ T')
    (hs : h ≫ t' = g ≫ p) (w : Z ⟶ T) (hw : h ≫ u = w) (hs' : w ≫ t = g ≫ p) :
    ((S.restrict u t' hu).γ Z g h hs).hom = (compIso h u w hw N).hom ≫ (S.γ Z g w hs').hom := by
  subst hw
  rfl

/-- Transfer of a descended structure along an isomorphism of modules. -/
def transfer {t : T ⟶ Y} {N : T.Modules} (S : Str D t N) {N' : T.Modules} (ψ : N' ≅ N) :
    Str D t N' where
  γ Z g h hs := (Scheme.Modules.pullback h).mapIso ψ ≪≫ S.γ Z g h hs
  nat Z Z' k g h hs g' h' hs' hg hh := by
    rw [Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom,
      tr_comp k hh hh hg, tr_map, ← S.nat]
  coc Z g₁ g₂ h hs₁ hs₂ hθ := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    rw [S.coc]

lemma Hom.transfer {t : T ⟶ Y} {N : T.Modules} (S : Str D t N) {N' : T.Modules}
    (ψ : N' ≅ N) : Hom (S.transfer ψ) S ψ.hom := by
  intro Z g h hs hs'
  rfl

lemma Hom.restrict {t t' : T ⟶ Y} {N N' : T.Modules} {S : Str D t N} {S' : Str D t' N'}
    {φ : N ⟶ N'} (hφ : Hom S S' φ) {T' : Scheme.{u}} (u : T' ⟶ T) (s s' : T' ⟶ Y)
    (hu : u ≫ t = s) (hu' : u ≫ t' = s') :
    Hom (S.restrict u s hu) (S'.restrict u s' hu') ((Scheme.Modules.pullback u).map φ) := by
  intro Z g h hs hs'
  have h₁ : (h ≫ u) ≫ t = g ≫ p := by rw [Category.assoc, hu, hs]
  have h₂ : (h ≫ u) ≫ t' = g ≫ p := by rw [Category.assoc, hu', hs']
  rw [restrict_γ S u s hu g h hs (h ≫ u) rfl h₁, restrict_γ S' u s' hu' g h hs' (h ≫ u) rfl h₂,
    compIso_naturality_assoc, hφ]

/-- Restricting twice is restricting along the composite. -/
lemma Hom.restrict_restrict {t : T ⟶ Y} {N : T.Modules} (S : Str D t N) {T' T'' : Scheme.{u}}
    (u : T' ⟶ T) (u' : T'' ⟶ T') (w : T'' ⟶ T) (hw : u' ≫ u = w) (s : T' ⟶ Y)
    (s' s'' : T'' ⟶ Y) (hu : u ≫ t = s) (hu' : u' ≫ s = s') (hw' : w ≫ t = s'') :
    Hom ((S.restrict u s hu).restrict u' s' hu') (S.restrict w s'' hw')
      (compIso u' u w hw N).hom := by
  intro Z g h hs hs'
  have hhw : (h ≫ u') ≫ u = h ≫ w := by rw [Category.assoc, hw]
  have hsw : (h ≫ w) ≫ t = g ≫ p := by rw [Category.assoc, hw', hs']
  have hsu : (h ≫ u') ≫ s = g ≫ p := by rw [Category.assoc, hu', hs]
  rw [restrict_γ S w s'' hw' g h hs' (h ≫ w) rfl hsw,
    restrict_γ (S.restrict u s hu) u' s' hu' g h hs (h ≫ u') rfl hsu,
    restrict_γ S u s hu g (h ≫ u') hsu (h ≫ w) hhw hsw,
    ← compIso_assoc_assoc h u' u (h ≫ u') w (h ≫ w) rfl hw rfl hhw N]

/-- A square comparison is compatible with the two iterated restrictions around the square. -/
lemma Hom.square {t : T ⟶ Y} {N : T.Modules} (S : Str D t N) {A B C : Scheme.{u}}
    (b : B ⟶ T) (f : A ⟶ C) (g : A ⟶ B) (c : C ⟶ T) (hsq : f ≫ c = g ≫ b)
    (sB : B ⟶ Y) (sC : C ⟶ Y) (s s' : A ⟶ Y) (hb : b ≫ t = sB) (hc : c ≫ t = sC)
    (hf : f ≫ sC = s) (hg : g ≫ sB = s') :
    Hom ((S.restrict c sC hc).restrict f s hf) ((S.restrict b sB hb).restrict g s' hg)
      (squarePullbackIso b f g c hsq N).hom := by
  have H₁ := Hom.restrict_restrict S c f (f ≫ c) rfl sC s (f ≫ c ≫ t) hc hf
    (by rw [Category.assoc])
  have H₂ := Hom.restrict_restrict S b g (f ≫ c) hsq.symm sB s' (f ≫ c ≫ t) hb hg
    (by rw [Category.assoc])
  have := Hom.comp (by rw [← hf, ← hc]) H₁ (Hom.inv H₂)
  rw [UnitCocycleDescentUniqueness.squarePullbackIso_hom_eq_compIso
    b f g c hsq (f ≫ c) rfl hsq.symm N]
  exact this

end Str

end Str

section Descend

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {F : X.Modules} {D : Datum p F} {T : Scheme.{u}}

namespace Str

lemma coc_inv {t : T ⟶ Y} {N : T.Modules} (S : Str D t N) (Z : Scheme.{u}) (g₁ g₂ : Z ⟶ X)
    (h : Z ⟶ T) (hs₁ : h ≫ t = g₁ ≫ p) (hs₂ : h ≫ t = g₂ ≫ p) (hθ : g₁ ≫ p = g₂ ≫ p) :
    (S.γ Z g₂ h hs₂).inv = (D.θ Z g₁ g₂ hθ).inv ≫ (S.γ Z g₁ h hs₁).inv := by
  rw [← cancel_epi (S.γ Z g₂ h hs₂).hom, Iso.hom_inv_id, ← S.coc Z g₁ g₂ h hs₁ hs₂ hθ]
  simp

/-- A morphism compatible with two descended structures is determined by its pullback to the
base change of `p`. -/
lemma hom_of_universal {t : T ⟶ Y} {N N' : T.Modules} (S : Str D t N) (S' : Str D t N')
    (φ : N ⟶ N')
    (H : (Scheme.Modules.pullback (pullback.snd p t)).map φ ≫
        (S'.γ _ (pullback.fst p t) (pullback.snd p t) pullback.condition.symm).hom =
      (S.γ _ (pullback.fst p t) (pullback.snd p t) pullback.condition.symm).hom) :
    Hom S S' φ := by
  intro Z g h hs hs'
  let ℓ : Z ⟶ pullback p t := pullback.lift g h hs.symm
  have hℓg : ℓ ≫ pullback.fst p t = g := pullback.lift_fst _ _ _
  have hℓh : ℓ ≫ pullback.snd p t = h := pullback.lift_snd _ _ _
  rw [S.nat _ Z ℓ (pullback.fst p t) (pullback.snd p t) pullback.condition.symm g h hs hℓg hℓh,
    S'.nat _ Z ℓ (pullback.fst p t) (pullback.snd p t) pullback.condition.symm g h hs' hℓg hℓh,
    ← tr_map ℓ hℓh φ, ← tr_comp, H]

/-- Uniqueness of morphisms compatible with two descended structures on line bundles. -/
lemma hom_ext [QuasiCompact p] [Flat p] [Surjective p] {t t' : T ⟶ Y} (ht : t = t')
    {N N' : T.Modules} (hN : IsLocallyFreeRankOne N) (hN' : IsLocallyFreeRankOne N')
    {S : Str D t N} {S' : Str D t' N'} {φ ψ : N ≅ N'} (hφ : Hom S S' φ.hom)
    (hψ : Hom S S' ψ.hom) : φ = ψ := by
  subst ht
  apply iso_ext_of_pullback (pullback.snd p t) hN hN'
  have h₁ := hφ _ (pullback.fst p t) (pullback.snd p t) pullback.condition.symm
    pullback.condition.symm
  have h₂ := hψ _ (pullback.fst p t) (pullback.snd p t) pullback.condition.symm
    pullback.condition.symm
  rw [← h₂] at h₁
  exact (cancel_mono _).1 h₁

/-- Existence of an isomorphism compatible with two descended structures on line bundles. -/
lemma exists_hom [QuasiCompact p] [Flat p] [Surjective p] {t : T ⟶ Y} {N N' : T.Modules}
    (hN : IsLocallyFreeRankOne N) (hN' : IsLocallyFreeRankOne N') (S : Str D t N)
    (S' : Str D t N') : ∃ φ : N ≅ N', Hom S S' φ.hom := by
  let γ := S.γ _ (pullback.fst p t) (pullback.snd p t) pullback.condition.symm
  let γ' := S'.γ _ (pullback.fst p t) (pullback.snd p t) pullback.condition.symm
  let e := γ ≪≫ γ'.symm
  have key : ∀ (U : Scheme.{u}) (a b : U ⟶ pullback p t)
      (h : a ≫ pullback.snd p t = b ≫ pullback.snd p t),
      tr a rfl rfl e.hom = tr b h.symm h.symm e.hom := by
    intro U a b h
    have hs : (a ≫ pullback.snd p t) ≫ t = (a ≫ pullback.fst p t) ≫ p := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    have hs' : (a ≫ pullback.snd p t) ≫ t = (b ≫ pullback.fst p t) ≫ p := by
      rw [h, Category.assoc, Category.assoc, pullback.condition]
    have hθ : (a ≫ pullback.fst p t) ≫ p = (b ≫ pullback.fst p t) ≫ p := hs.symm.trans hs'
    simp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [tr_comp a rfl rfl rfl, tr_comp b h.symm rfl h.symm,
      ← S.nat _ U a _ _ _ _ _ hs rfl rfl, ← S.nat _ U b _ _ _ _ _ hs' rfl h.symm,
      ← inv_eq_tr a rfl rfl γ' (S'.γ U _ _ hs) (S'.nat _ U a _ _ _ _ _ hs rfl rfl),
      ← inv_eq_tr b h.symm rfl γ' (S'.γ U _ _ hs') (S'.nat _ U b _ _ _ _ _ hs' rfl h.symm),
      ← S.coc U _ _ _ hs hs' hθ, S'.coc_inv U _ _ _ hs hs' hθ]
    simp
  obtain ⟨φ, hφ, -⟩ := LineBundleIsoDescent.lineBundleIsoDescent _ _ (pullback.snd p t)
    inferInstance inferInstance inferInstance N N' hN hN' e
    (fun U a b h ↦ compat_of_tr_eq _ e.hom a b h (a ≫ pullback.snd p t) rfl h.symm (key U a b h))
  refine ⟨φ, hom_of_universal S S' φ.hom ?_⟩
  have hφ' : (Scheme.Modules.pullback (pullback.snd p t)).map φ.hom = e.hom :=
    congrArg Iso.hom hφ
  rw [hφ']
  simp [e, γ, γ']

end Str

end Descend

end Langlands.Scheme.Modules.LineBundleFlatDescent
