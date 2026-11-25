/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LatticeSectionMatrix
import WeilConjectures.AlgebraicGeometry.LatticePairMatrixAtBasis

/-!
# Continuous matrices for locally free integral lattice pairs

Source: Bhatt--Scholze, Proposition 6.8.4(6), local bases
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- An integral lattice pair has locally an invertible continuous matrix in a fixed
rational frame, with its embedded-image formula after every restriction.
Source: Bhatt--Scholze, Proposition 6.8.4(6), local integral bases
(auxiliary; not a blueprint node).
Proof: use the finite locally free presentation of the integral module. The sieve of
objects mapping to a chosen basis object covers the identity slice object, hence its
corresponding sieve covers V. On each such object apply the matrix-at-basis calculation.
This uses the varying-rank definition of finite local freeness without adding a fixed
rank hypothesis to the integral module. -/
theorem integralLatticePair_localMatrix (X : Scheme.{u})
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K)
    (L : SheafOfModules.{u + 1} (latticeModuleRing X K))
    (U : X.ProEt) (n : ℕ) (e : L.over U ≅ latticeFreeSheaf X K U n)
    (V : X.ProEt) (f : V ⟶ U)
    (P : IntegralLatticePair (latticeCoefficientSheafMap X A.subtype continuous_subtype_val)
      L V) :
    ∃ S : Sieve V, S ∈ Scheme.ProEt.topology X V ∧
      ∀ (W : X.ProEt) (a : W ⟶ V), S a →
        ∃ G : Matrix.GeneralLinearGroup (Fin n)
            ((latticeCoefficientSheaf X K).obj.obj (op W)),
          ∀ T : Over W,
            Set.image (e.hom.val.app (op (Over.mk (T.hom ≫ a ≫ f))))
              (P.image (op (Over.mk (T.hom ≫ a)))) =
            sectionMatrixLatticeImage X K A U n (op (Over.mk (T.hom ≫ a ≫ f)))
              (Matrix.GeneralLinearGroup.map
                (((latticeCoefficientSheaf X K).obj.map T.hom.op).hom) G) := by
  classical
  obtain ⟨q, hq, hf⟩ := P.locallyFree.exists_localGeneratorsData
  let := hq
  let := hf
  let I : Over V := Over.mk (𝟙 V)
  refine ⟨Sieve.overEquiv I (Sieve.ofObjects q.X I), ?_, ?_⟩
  · exact q.coversTop I
  · intro W a ha
    rw [Sieve.overEquiv_iff, Sieve.mem_ofObjects_iff] at ha
    obtain ⟨i, ⟨t⟩⟩ := ha
    have ht : Over.mk a ⟶ q.X i := by
      change Over.mk (a ≫ 𝟙 V) ⟶ q.X i at t
      exact eqToHom (congrArg (fun b : W ⟶ V ↦ Over.mk b)
        (Category.comp_id a).symm) ≫ t
    exact integralLatticePair_matrixAtBasis X K A L U n e V f P q i W a ht

end AlgebraicGeometry.ProEtale
