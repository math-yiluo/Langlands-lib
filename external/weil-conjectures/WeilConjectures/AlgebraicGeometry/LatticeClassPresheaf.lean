/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
import WeilConjectures.AlgebraicGeometry.StrictPerfectPackageOnSite
public import WeilConjectures.AlgebraicGeometry.LatticeSheafBasic
import WeilConjectures.AlgebraicGeometry.LatticePairRestriction
/-!
# The presheaf of embedded lattice images

Source: Bhatt--Scholze, Proposition 6.8.4(6), pp. 59–60.
(auxiliary; not a blueprint node).
-/

@[expose] public section

attribute [local instance] AlgebraicGeometry.ProEtale.latticeWeakSheafifyOver
  AlgebraicGeometry.Scheme.strictPerfectSliceLocallyBijective
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtale
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{u}}
  {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
  (L : SheafOfModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))

def LatticeImageClass (U : X.ProEt) :=
  {s : ∀ T : Over U, Set (L.val.obj (op T.left)) //
    ∃ P : IntegralLatticePair a L U, ∀ T, P.image (op T) = s T}

noncomputable def latticeImageClass (U : X.ProEt) (P : IntegralLatticePair a L U) :
    LatticeImageClass a L U := ⟨fun T ↦ P.image (op T), P, fun _ ↦ rfl⟩

noncomputable def latticeImageClassMap {U V : X.ProEt} (f : V ⟶ U)
    (s : LatticeImageClass a L U) : LatticeImageClass a L V :=
  ⟨fun T ↦ s.val ((Over.map f).obj T), by
    obtain ⟨P, hP⟩ := s.property
    exact ⟨P.restrict a f, fun T ↦ (P.restrict_image a f (op T)).trans (hP _)⟩⟩

noncomputable def latticeClassPresheaf : X.ProEtᵒᵖ ⥤ Type (u + 2) where
  obj U := ULift.{u + 2} (LatticeImageClass a L U.unop)
  map f := ↾fun s ↦ ULift.up (latticeImageClassMap a L f.unop s.down)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    apply Subtype.ext
    funext T
    obtain ⟨W, t, rfl⟩ := T.mk_surjective
    change s.down.val (Over.mk (t ≫ 𝟙 _)) = s.down.val (Over.mk t)
    rw [Category.comp_id]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    apply Subtype.ext
    funext T
    obtain ⟨W, t, rfl⟩ := T.mk_surjective
    change s.down.val (Over.mk (t ≫ (g.unop ≫ f.unop))) =
      s.down.val (Over.mk ((t ≫ g.unop) ≫ f.unop))
    rw [Category.assoc]
theorem latticeImageClass_eq_of_cover {U : X.ProEt}
    (ha : ∀ T, Function.Injective (((latticeScalarMap a U).hom.app T).hom))
    (s t : LatticeImageClass a L U) (r : Sieve U)
    (hr : r ∈ (Scheme.ProEt.topology X) U)
    (h : ∀ (V : X.ProEt) (f : V ⟶ U), r f →
      latticeImageClassMap a L f s = latticeImageClassMap a L f t) : s = t := by
  classical
  obtain ⟨P, hP⟩ := s.property
  obtain ⟨Q, hQ⟩ := t.property
  have hlocal (W : Over U) (hW : r W.hom) : P.image (op W) = Q.image (op W) := by
    have he := congrArg (fun z ↦ z.val (Over.mk (𝟙 W.left))) (h W.left W.hom hW)
    change s.val (Over.mk (𝟙 W.left ≫ W.hom)) =
      t.val (Over.mk (𝟙 W.left ≫ W.hom)) at he
    rw [Category.id_comp] at he
    have hW' : Over.mk W.hom = W := by
      obtain ⟨Z, f, rfl⟩ := W.mk_surjective
      rfl
    rw [hW'] at he
    exact (hP W).trans (he.trans (hQ W).symm)
  have hle (P' Q' : IntegralLatticePair a L U)
      (hl : ∀ W : Over U, r W.hom → P'.image (op W) = Q'.image (op W))
      (T : Over U) : P'.image (op T) ⊆ Q'.image (op T) := by
    intro x hx
    let v := (Sieve.overEquiv T).symm (r.pullback T.hom)
    have hv : v ∈ ((Scheme.ProEt.topology X).over U) T :=
      (Scheme.ProEt.topology X).overEquiv_symm_mem_over T _
        ((Scheme.ProEt.topology X).pullback_stable T.hom hr)
    apply IntegralLatticePair.mem_image_of_locally_mem a L U ha Q' T x v hv
    intro W f hf
    have hw : r W.hom := by
      change r (f.left ≫ T.hom) at hf
      rwa [Over.w f] at hf
    rw [← hl W hw]
    exact IntegralLatticePair.map_mem_image a L U P' f hx
  apply Subtype.ext
  funext T
  rw [← hP T, ← hQ T]
  exact Set.Subset.antisymm (hle P Q hlocal T)
    (hle Q P (fun W hw ↦ (hlocal W hw).symm) T)

/-- Equality of represented image families is local.
Source: Bhatt--Scholze, Proposition 6.8.4(6), descent of embedded lattices.
(auxiliary; not a blueprint node).
Proof: equal restrictions of two amalgamations give equal image families on the
cover. Pull that cover back to every slice test object. Local membership in each
integral image gives both inclusions there, hence equality of the families. -/
theorem latticeClassPresheaf_isSeparated
    (ha : ∀ (U : X.ProEt) T,
      Function.Injective (((latticeScalarMap a U).hom.app T).hom)) :
    Presieve.IsSeparated (Scheme.ProEt.topology X) (latticeClassPresheaf a L) := by
  intro U r hr x s t hs ht
  apply ULift.ext
  apply latticeImageClass_eq_of_cover a L (ha U) s.down t.down r hr
  intro V f hf
  exact congrArg ULift.down ((hs f hf).trans (ht f hf).symm)

end AlgebraicGeometry.ProEtale
