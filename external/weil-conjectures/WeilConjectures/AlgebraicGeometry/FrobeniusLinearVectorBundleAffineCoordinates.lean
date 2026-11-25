/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.CharP.Basic
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.EtaleTensorHomEvaluationNaturality
import WeilConjectures.AlgebraicGeometry.FrobeniusLinearFreeFrameCoordinates

/-!
# Natural affine coordinates for Frobenius-linear vector bundles

Source: Stacks Project, `more-etale.tex`, Tag 0GKU, lines 4213--4270
(blueprint: lem-fd-frobenius-linear-vector-bundle-affine-coordinates).

This is the affine coordinate comparison used in the polynomial solution construction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
namespace Scheme
open Modules

attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj

/-- Finite local freeness supplies an affine tensor-pullback frame near each point. -/
private theorem exists_affine_tensor_frame (S : Scheme.{u}) (E : S.Modules) [E.IsFiniteLocallyFree]
    (U : S.Etale) (x : U.left) :
    ∃ (V : S.Etale) (g : V ⟶ U) (v : V.left),
      g.left v = x ∧ IsAffine V.left ∧
      ∃ n : ℕ, Nonempty ((Modules.tensorPullback V.hom).obj E ≅
        SheafOfModules.free (R := V.left.ringCatSheaf) (ULift.{u} (Fin n))) := by
  classical
  let G := (Modules.tensorPullback U.hom).obj E
  have : G.IsFiniteLocallyFree :=
    Modules.isFiniteLocallyFree_of_iso
      ((Modules.tensorSectionsPullbackComparison U.hom).app E).symm
  obtain ⟨A, κ, hκ, hxA, ⟨α⟩⟩ := Modules.exists_restrict_iso_free_of_isFiniteLocallyFree G x
  let : Finite κ := hκ
  let : Fintype κ := Fintype.ofFinite κ
  obtain ⟨B, hB, hxB, hBA⟩ := exists_isAffineOpen_mem_and_subset (X := U.left)
    (x := x) (U := A) hxA
  let : IsAffine B.toScheme := hB
  let V : S.Etale := Scheme.Etale.mk (B.ι ≫ U.hom)
  let g : V ⟶ U := MorphismProperty.Over.homMk B.ι rfl
  refine ⟨V, g, ⟨x, hxB⟩, rfl, hB, Fintype.card κ, ⟨?_⟩⟩
  let k := U.left.homOfLE hBA
  have hk : k ≫ A.ι = B.ι := by simp [k]
  let eqκ : κ ≃ ULift.{u} (Fin (Fintype.card κ)) :=
    (Fintype.equivFin κ).trans Equiv.ulift.symm
  exact (Modules.tensorSectionsComp B.ι U.hom).symm.app E ≪≫
    (Modules.tensorSectionsPullbackComparison B.ι).app G ≪≫
    (Modules.restrictFunctorIsoPullback B.ι).symm.app G ≪≫
    Modules.restrictCompIso G A.ι k B.ι hk ≪≫
    (Modules.restrictFunctor k).mapIso α ≪≫
    Modules.restrictFreeIso k κ ≪≫
    SheafOfModules.freeFunctor.mapIso eqκ.toIso

/-- Around every point, the Frobenius-linear sheaf map has a matrix expression
in coordinates compatible with pullback to every étale object over the chart.

Source: Stacks Project, Tag 0GKU, lemma-frobenius-linear-on-vb, first paragraph.
(blueprint: lem-fd-frobenius-linear-vector-bundle-affine-coordinates).

Proof: pull the finite locally free module back to U and trivialize it near x.
Refine the trivializing open to an affine open V containing x. A finite frame on
V pulls back to a frame on every étale W over V. Sending a section to its frame
coordinates gives the additive equivalences e. Pullback of the frame and its dual
frame commutes with composition: the tensor-pullback comparison is normalized by
its adjunction unit, and therefore carries restricted basis sections to the same
basis sections. Hence e commutes with restriction on every section over V. Define
a(i,j) to be the i-th coordinate of F applied to the j-th frame section on V.
Naturality of F makes their restrictions the coefficients on W. Expanding a section
in the pulled-back frame, additivity and the given Frobenius scalar law give the
displayed matrix formula. The structural map from F_p makes the section ring of V
have characteristic p. Rank zero uses the unique empty coordinate vector. Empty U
has no point x to consider. No quasi-compactness or separation of S is used.
-/
theorem exists_frobenius_linear_vector_bundle_affine_coordinates
    (p : ℕ) [Fact p.Prime]
    (S : Scheme.{u}) [S.Over (Spec (.of (ULift.{u} (ZMod p))))]
    (E : S.Modules) [E.IsQuasicoherent] [E.IsFiniteLocallyFree]
    (F : (Modules.etaleTensorSectionsSheaf E) ⟶ Modules.etaleTensorSectionsSheaf E)
    (hF : ∀ (U : S.Etale) (a : Γ(U.left, ⊤))
      (e : Γ((Modules.tensorPullback U.hom).obj E, ⊤)),
      F.hom.app (op U)
          ((((Modules.tensorPullback U.hom).obj E).smul a).asHom.hom e) =
        (((Modules.tensorPullback U.hom).obj E).smul (a ^ p)).asHom.hom
          (F.hom.app (op U) e)) :
    ∀ (U : S.Etale) (x : U.left),
      ∃ (V : S.Etale) (g : V ⟶ U) (v : V.left),
        g.left v = x ∧ IsAffine V.left ∧ CharP Γ(V.left, ⊤) p ∧
        ∃ (n : ℕ)
          (e : ∀ (W : S.Etale), (W ⟶ V) →
            Γ((Modules.tensorPullback W.hom).obj E, ⊤) ≃+ (Fin n → Γ(W.left, ⊤)))
          (a : Fin n → Fin n → Γ(V.left, ⊤)),
          (∀ (W : S.Etale) (h : W ⟶ V)
            (m : Γ((Modules.tensorPullback V.hom).obj E, ⊤)) (i : Fin n),
            e W h ((Modules.etaleTensorSectionsSheaf E).obj.map h.op m) i =
              h.left.appTop (e V (𝟙 V) m i)) ∧
          (∀ (W : S.Etale) (h : W ⟶ V)
            (m : Γ((Modules.tensorPullback W.hom).obj E, ⊤)) (i : Fin n),
            e W h (F.hom.app (op W) m) i =
              ∑ j, h.left.appTop (a i j) * (e W h m j) ^ p) := by
  intro U x
  obtain ⟨V, g, v, hv, hV, n, ⟨α⟩⟩ := exists_affine_tensor_frame S E U x
  have : Nontrivial Γ(V.left, ⊤) :=
    (V.left.presheaf.germ ⊤ v trivial).hom.domain_nontrivial
  let ρ : ULift.{u} (ZMod p) →+* Γ(V.left, ⊤) :=
    ((Scheme.ΓSpecIso (.of (ULift.{u} (ZMod p)))).inv ≫
      (S ↘ Spec (.of (ULift.{u} (ZMod p)))).appTop ≫ V.hom.appTop).hom
  have hc : CharP Γ(V.left, ⊤) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
      rw [← map_natCast ρ, CharP.cast_eq_zero (ULift.{u} (ZMod p)) p, map_zero])
  obtain ⟨e, a, henat, heF⟩ := frobenius_linear_free_frame_coordinates p S E F hF V n α
  exact ⟨V, g, v, hv, hV, hc, n, e, a, henat, heF⟩

end Scheme
end AlgebraicGeometry
