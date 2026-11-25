/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
import WeilConjectures.AlgebraicGeometry.AffineTopTensorSections
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsTransport
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Normalized affine tensor sections

Source: Stacks Project, Tags 01I9, 01IA and 03DR.
(blueprint: new-etale-affine-tensor-sections-equiv) -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj

attribute [local instance 2000]
  Modules.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

private theorem tensorQuasicoherent {A B : Scheme.{u}} (f : A ⟶ B)
    (M : B.Modules) [M.IsQuasicoherent] :
    ((Modules.tensorPullback f).obj M).IsQuasicoherent := by
  let e : Modules.tensorPullback f ≅ Modules.pullback f :=
    (Modules.nonempty_tensorPullbackAdjunction f).some.leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction f)
  exact (SheafOfModules.isQuasicoherent A.ringCatSheaf).prop_of_iso (e.app M).symm
    (inferInstance : ((Modules.pullback f).obj M).IsQuasicoherent)

-- Compare tensor-product scalar instances and sectionwise module morphisms.
/-- Over affine objects, tensoring coefficient sections with the target ring gives
sections on the target, with the unit-normalized restriction formula.
Source: Stacks Project, Tags 01I9, 01IA and 03DR.
(blueprint: new-etale-affine-tensor-sections-equiv)

Proof: compare tensorPullback U.hom with ordinary pullback through the unique
isomorphism of left adjoints to pushforward U.hom.  Ordinary pullback preserves
quasi-coherence, so the tensor pullback of F is quasi-coherent.  Apply the affine
pullback sections formula to a.left on the whole affine schemes U and V.  Its
pure-tensor formula is c(m tensor b) = b times the adjunction-unit pullback of m.
Compose with the global-sections isomorphism induced by tensorSectionsComp,
then transport along a.w.  Both are linear for functions on V.  The definition
of etaleTensorSectionsRestriction therefore gives the displayed equation.
The affine sections map is bijective, and the composition and equality transports
are isomorphisms, giving an additive equivalence.  This argument includes the
zero module and empty affine schemes.
-/
theorem exists_etaleAffineTensorSectionsEquiv
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U V : X.Etale) (a : V ⟶ U) (hU : IsAffine U.left) (hV : IsAffine V.left) :
    letI : Algebra Γ(U.left, ⊤) Γ(V.left, ⊤) := a.left.appTop.hom.toAlgebra
    ∃ e : (Γ((Modules.tensorPullback U.hom).obj F, ⊤) ⊗[Γ(U.left, ⊤)]
      Γ(V.left, ⊤)) ≃+ Γ((Modules.tensorPullback V.hom).obj F, ⊤),
      ∀ (m : Γ((Modules.tensorPullback U.hom).obj F, ⊤)) (b : Γ(V.left, ⊤)),
        e (m ⊗ₜ[Γ(U.left, ⊤)] b) = b • Modules.etaleTensorSectionsRestriction F a m  := by
  classical
  let : Algebra Γ(U.left, ⊤) Γ(V.left, ⊤) := a.left.appTop.hom.toAlgebra
  let : IsAffine U.left := hU
  let : IsAffine V.left := hV
  let G : U.left.Modules := (Modules.tensorPullback U.hom).obj F
  have hG : G.IsQuasicoherent := tensorQuasicoherent U.hom F
  obtain ⟨d, hd, hpure⟩ := exists_affineTopTensorSections a.left G hG hU hV
  obtain ⟨e, he⟩ := Modules.exists_etaleTensorSectionsTransport F a
  refine ⟨(AddEquiv.ofBijective d hd).trans e, ?_⟩
  intro m b
  exact (congrArg e (hpure m b)).trans (he m b)

end
end AlgebraicGeometry.Scheme
