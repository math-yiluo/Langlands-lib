import Langlands.GroupScheme.RelativeUnipotent.LinearFreeBundleIso

/-! # Faithful actual module comparisons of vector-group charts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.VectorModuleComparison

/-- The canonical pulled-back basis is the original free basis transported
through the actual free-pullback comparison. -/
lemma basis_freePullback {S : Scheme.{u}} (n : ℕ) (T : Over S) (i : Fin n) :
    freeBundleBasis n T i =
      (freePullbackIso T.hom (ULift.{u} (Fin n))).inv.app ⊤
        (FreeBundleMatrices.generator T.left n i) := by
  rw [freeBundleBasis, Module.Basis.reindex_apply, globalSectionBasis_apply]
  rfl

variable {R : CommRingCat.{u}} {n m l : ℕ}

/-- Compatibility of an actual group map and an actual module map in the
same canonical all-test coordinates. -/
def Compatible (φ : VectorGroup.groupScheme R n ⟶ VectorGroup.groupScheme R m)
    (f : freeBundle (Spec R) n ⟶ freeBundle (Spec R) m) : Prop :=
  ∀ (T : Over (Spec R)) (x : T ⟶ (VectorGroup.groupScheme R n).X),
    (freeVectorBundlePoints R m T (x ≫ φ.hom.hom)).toAdd =
      ((Scheme.Modules.pullback T.hom).map f).app ⊤
        (freeVectorBundlePoints R n T x).toAdd

/-- Canonical all-test point sections detect the actual coefficient module map. -/
lemma moduleHom_ext
    (f g : freeBundle (Spec R) n ⟶ freeBundle (Spec R) m)
    (h : ∀ (T : Over (Spec R)) (x : T ⟶ (VectorGroup.groupScheme R n).X),
      ((Scheme.Modules.pullback T.hom).map f).app ⊤ (freeVectorBundlePoints R n T x).toAdd =
        ((Scheme.Modules.pullback T.hom).map g).app ⊤ (freeVectorBundlePoints R n T x).toAdd) :
    f = g := by
  let T : Over (Spec R) := Over.mk (𝟙 (Spec R))
  let P := Scheme.Modules.pullback (𝟙 (Spec R))
  let : P.Faithful := Functor.Faithful.of_iso (Scheme.Modules.pullbackId (Spec R)).symm
  apply P.map_injective
  let e := (freePullbackIso T.hom (ULift.{u} (Fin n))).symm
  apply (cancel_epi e.hom).mp
  apply FreeBundleMatrices.hom_ext
  intro i
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  change (P.map f).app ⊤
      ((freePullbackIso T.hom (ULift.{u} (Fin n))).inv.app ⊤
        (FreeBundleMatrices.generator T.left n i)) =
    (P.map g).app ⊤
      ((freePullbackIso T.hom (ULift.{u} (Fin n))).inv.app ⊤
        (FreeBundleMatrices.generator T.left n i))
  rw [← basis_freePullback n T i]
  let x := (freeVectorBundlePoints R n T).symm (Multiplicative.ofAdd (freeBundleBasis n T i))
  have H := h T x
  have hx : (freeVectorBundlePoints R n T x).toAdd = freeBundleBasis n T i :=
    congrArg Multiplicative.toAdd ((freeVectorBundlePoints R n T).apply_symm_apply
      (Multiplicative.ofAdd (freeBundleBasis n T i)))
  rw [hx] at H
  exact H

/-- Two actual module maps compatible with the same original group map agree. -/
lemma Compatible.unique
    {φ : VectorGroup.groupScheme R n ⟶ VectorGroup.groupScheme R m}
    {f g : freeBundle (Spec R) n ⟶ freeBundle (Spec R) m}
    (hf : Compatible φ f) (hg : Compatible φ g) : f = g :=
  moduleHom_ext f g (fun T x => (hf T x).symm.trans (hg T x))

/-- Compatibility is preserved by actual composition of both maps. -/
lemma Compatible.comp
    {φ : VectorGroup.groupScheme R n ⟶ VectorGroup.groupScheme R m}
    {ψ : VectorGroup.groupScheme R m ⟶ VectorGroup.groupScheme R l}
    {f : freeBundle (Spec R) n ⟶ freeBundle (Spec R) m}
    {g : freeBundle (Spec R) m ⟶ freeBundle (Spec R) l}
    (hf : Compatible φ f) (hg : Compatible ψ g) :
    Compatible (φ ≫ ψ) (f ≫ g) := by
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, hg T, hf T,
    Functor.map_comp, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]

/-- A compatible actual pair of isomorphisms retains compatibility on inverses. -/
lemma Compatible.inv
    {e : VectorGroup.groupScheme R n ≅ VectorGroup.groupScheme R m}
    {f : freeBundle (Spec R) n ≅ freeBundle (Spec R) m}
    (h : Compatible e.hom f.hom) : Compatible e.inv f.inv := by
  intro T x
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullback T.hom).mapIso f).hom.app ⊤)).injective
  have H := h T (x ≫ e.inv.hom.hom)
  have hx : (x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x := by
    rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom,
      Category.comp_id]
  rw [hx] at H
  change ((Scheme.Modules.pullback T.hom).map f.hom).app ⊤
      (freeVectorBundlePoints R n T (x ≫ e.inv.hom.hom)).toAdd =
    ((Scheme.Modules.pullback T.hom).map f.hom).app ⊤
      (((Scheme.Modules.pullback T.hom).map f.inv).app ⊤
        (freeVectorBundlePoints R m T x).toAdd)
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    ← Functor.map_comp, f.inv_hom_id, CategoryTheory.Functor.map_id,
    Scheme.Modules.Hom.id_app]
  exact H.symm

/-- An actual module isomorphism that implements the original vector-group
isomorphism on every scheme test. -/
structure Comparison (e : VectorGroup.groupScheme R n ≅ VectorGroup.groupScheme R m) where
  moduleIso : freeBundle (Spec R) n ≅ freeBundle (Spec R) m
  compatible : Compatible e.hom moduleIso.hom

namespace Comparison

variable {e : VectorGroup.groupScheme R n ≅ VectorGroup.groupScheme R m}

/-- The actual module comparison of an original positive-weight quotient comparison. -/
def ofWeight {d : ℕ} (hd : 0 < d)
    (he : VectorGroup.HasScalarWeight (VectorGroup.pointTransformation e.hom) d) :
    Comparison e :=
  ⟨LinearFreeBundleIso.moduleIso e hd he, LinearFreeBundleIso.moduleIso_sections e hd he⟩

/-- The actual module comparison is uniquely determined by the original group map. -/
lemma unique (C D : Comparison e) : C.moduleIso = D.moduleIso :=
  Iso.ext (C.compatible.unique D.compatible)

/-- Composition of actual compatible comparisons. -/
def trans {f : VectorGroup.groupScheme R m ≅ VectorGroup.groupScheme R l}
    (C : Comparison e) (D : Comparison f) : Comparison (e ≪≫ f) where
  moduleIso := C.moduleIso ≪≫ D.moduleIso
  compatible := C.compatible.comp D.compatible

/-- Inverse of an actual compatible comparison. -/
def symm (C : Comparison e) : Comparison e.symm where
  moduleIso := C.moduleIso.symm
  compatible := C.compatible.inv

end Comparison
end Langlands.GroupScheme.RelativeUnipotent.VectorModuleComparison
