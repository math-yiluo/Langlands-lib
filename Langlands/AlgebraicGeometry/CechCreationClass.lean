import Langlands.AlgebraicGeometry.CechCreationDescent

/-! # Cup creation depends only on the one-cocycle class -/

noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.Cohomology.Cech

section Homotopy

variable {C : Type*} [Category* C] [Preadditive C]
  (K Q : CochainComplex C ℕ)
  (c c' : ∀ n, K.X n ⟶ Q.X (n + 1))
  (hc : ∀ n, K.d n (n + 1) ≫ c (n + 1) = -(c n ≫ Q.d (n + 1) (n + 2)))
  (hc' : ∀ n, K.d n (n + 1) ≫ c' (n + 1) = -(c' n ≫ Q.d (n + 1) (n + 2)))

set_option backward.isDefEq.respectTransparency false in
/-- A degree-zero cochain homotopy identifies two degree-raising homology maps. -/
lemma creationHomologyMap_eq_of_homotopy
    (h : ∀ n, K.X n ⟶ Q.X n)
    (hcc : ∀ n, c n = h n ≫ Q.d n (n + 1) - K.d n (n + 1) ≫ h (n + 1) + c' n)
    (n : ℕ) [K.HasHomology n] [Q.HasHomology (n + 1)] :
    creationHomologyMap K Q c hc n = creationHomologyMap K Q c' hc' n := by
  apply (cancel_epi (K.homologyπ n)).mp
  apply (cancel_mono (Q.homologyι (n + 1))).mp
  simp only [Category.assoc]
  change (K.sc n).homologyπ ≫
      ShortComplex.homologyMap (creationShortComplexMap K Q c hc n) ≫
        (Q.sc (n + 1)).homologyι =
    (K.sc n).homologyπ ≫
      ShortComplex.homologyMap (creationShortComplexMap K Q c' hc' n) ≫
        (Q.sc (n + 1)).homologyι
  rw [ShortComplex.π_homologyMap_ι, ShortComplex.π_homologyMap_ι,
    creationShortComplexMap_τ₂, creationShortComplexMap_τ₂]
  change K.iCycles n ≫ c n ≫ Q.pOpcycles (n + 1) =
    K.iCycles n ≫ c' n ≫ Q.pOpcycles (n + 1)
  rw [hcc n]
  simp only [Preadditive.comp_add, Preadditive.comp_sub, Preadditive.add_comp,
    Preadditive.sub_comp, Category.assoc, HomologicalComplex.d_pOpcycles,
    comp_zero]
  rw [← Category.assoc (K.iCycles n) (K.d n (n + 1)), HomologicalComplex.iCycles_d,
    zero_comp, sub_self, zero_add]

end Homotopy

section Cochains

open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R)
  [∀ W : X.Opens, Algebra R Γ(X, W)]
  (halg : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom π W).hom)
  {ι : Type w} (U : ι → X.Opens)

/-- Multiplication by a zero-cochain as an additive endomorphism. -/
def cupZeroAddHom (h : C (ab X.presheaf) U 0) (n : ℕ) :
    (complex (ab X.presheaf) U).X n ⟶ (complex (ab X.presheaf) U).X n :=
  AddCommGrpCat.ofHom
    { toFun := cup₀ X.presheaf U h
      map_zero' := cup₀_zero_right h
      map_add' := fun b b' => by
        funext τ
        simp only [cup₀_apply, Pi.add_apply, mul_add] }

set_option backward.isDefEq.respectTransparency false in
/-- Changing the creating one-cocycle by a coboundary leaves its homology map unchanged. -/
lemma cup₁HomologyMap_eq_of_sub_eq_d
    (z z' : C (ab X.presheaf) U 1)
    (hz : d (ab X.presheaf) U 1 z = 0) (hz' : d (ab X.presheaf) U 1 z' = 0)
    (h : C (ab X.presheaf) U 0) (hh : z - z' = d (ab X.presheaf) U 0 h)
    (n : ℕ) :
    cup₁HomologyMap π halg U z hz n = cup₁HomologyMap π halg U z' hz' n := by
  apply creationHomologyMap_eq_of_homotopy
    (h := cupZeroAddHom U h)
  intro m
  change cup₁AddHom π halg U z m =
    cupZeroAddHom U h m ≫ (complex (ab X.presheaf) U).d m (m + 1) -
      (complex (ab X.presheaf) U).d m (m + 1) ≫ cupZeroAddHom U h (m + 1) +
        cup₁AddHom π halg U z' m
  dsimp only [complex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of]
  rw [CochainComplex.of_d]
  ext b
  change cup₁ X.presheaf U z b =
    d (ab X.presheaf) U m (cup₀ X.presheaf U h b) -
      cup₀ X.presheaf U h (d (ab X.presheaf) U m b) + cup₁ X.presheaf U z' b
  rw [d_cup₀, add_sub_cancel_right, ← cup₁_add_left, ← hh, sub_add_cancel]

end Cochains

end Langlands.Cohomology.Cech
