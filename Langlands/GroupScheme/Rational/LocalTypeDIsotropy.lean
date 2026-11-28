import Langlands.GroupScheme.Reductive.AlmostSimpleGeometricBaseChange
import Langlands.GroupScheme.Reductive.PinningFieldBaseChange
import Langlands.GroupScheme.Reductive.StarActionIndependenceProof
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof
import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicTypeAProof
import Langlands.LinearAlgebra.ClassicalCartanDeterminants

/-! # Isotropy of type D at nonarchimedean places -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 100000

private local instance affineBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [IsAffineHom G.X.hom] : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›

private local instance finiteTypeBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [LocallyOfFiniteType G.X.hom] : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹LocallyOfFiniteType G.X.hom›

/-- Absolute almost-simplicity persists under every field extension. -/
theorem IsAbsolutelyAlmostSimple.baseChange_field
    {F L : Type u} [Field F] [Field L] [Algebra F L]
    {G : GroupScheme (Spec (CommRingCat.of F))} (hG : IsAbsolutelyAlmostSimple G) :
    IsAbsolutelyAlmostSimple ((GroupScheme.baseChange (algebraBaseMap F L)).obj G) := by
  let e := algebraicClosureEmbedding F L
  let : Algebra (AlgebraicClosure F) (AlgebraicClosure L) := e.toRingHom.toAlgebra
  have h := hG.2.baseChange_of_isAlgClosed (K := AlgebraicClosure L)
  have h' := h.of_iso ((algebraicClosureBaseChangeIso F L).app G).symm
  exact ⟨IsAlmostSimple.of_fieldExtension (K := AlgebraicClosure L) h', h'⟩

/-- The absolute Cartan matrices of the actual indices before and after an
arbitrary field extension agree up to a vertex equivalence. -/
theorem TitsIndexData.exists_cartan_equiv_of_fieldExtension
    {F L : Type u} [Field F] [Field L] [Algebra F L]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G)
    (dL : TitsIndexData ((GroupScheme.baseChange (algebraBaseMap F L)).obj G)) :
    ∃ v : d.Vertex ≃ dL.Vertex, ∀ a b, dL.cartan (v a) (v b) = d.cartan a b := by
  let Fₛ := SeparableClosure F
  let Lₛ := SeparableClosure L
  let E := AlgebraicClosure L
  let φ : Fₛ →ₐ[F] E := IsAlgClosed.lift
  let : Algebra Fₛ E := φ.toRingHom.toAlgebra
  let : IsScalarTower F Fₛ E := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  let p := d.pinning.toSplitPinning
  let q := dL.pinning.toSplitPinning
  let pE := p.baseChangeField (K := E)
  let qE := q.baseChangeField (K := E)
  let iso := (baseChangeFieldTowerIso F Fₛ E G).symm ≪≫
    baseChangeFieldTowerIso F L E G ≪≫ baseChangeFieldTowerIso L Lₛ E _
  obtain ⟨a⟩ := nonempty_rootDatumEquiv_of_iso pE.isConnectedReductive qE.isConnectedReductive
    pE.isSplitTorus qE.isSplitTorus pE.isMaximalTorus qE.isMaximalTorus iso
    pE.isRootDatum qE.isRootDatum
  obtain ⟨w, _, hw⟩ := StarActionIndependence.exists_weyl_comp_preserves_base pE qE a
  let r := RootPairing.Equiv.comp w a
  let v : d.Vertex ≃ dL.Vertex := (p.baseChangeSimpleEquiv (F := E)).trans
    ((r.indexEquiv.subtypeEquiv hw).trans (q.baseChangeSimpleEquiv (F := E)).symm)
  refine ⟨v, fun x y => ?_⟩
  exact ((q.baseChangeRootDatumEquiv (F := E)).symm.comp
    (r.comp (p.baseChangeRootDatumEquiv (F := E)))).toHom.pairing

private theorem not_typeA_of_typeD
    {n m : ℕ} (hn : 4 ≤ n) (f : Fin n ≃ Fin m)
    (h : ∀ i j, CartanMatrix.D n i j = CartanMatrix.A m (f i) (f j)) : False := by
  have hm := (Nat.card_fin n).symm.trans ((Nat.card_congr f).trans (Nat.card_fin m))
  subst m
  have hM : CartanMatrix.D n = (CartanMatrix.A n).submatrix f f := by
    ext i j
    exact h i j
  have hd := congrArg Matrix.det hM
  rw [Matrix.det_submatrix_equiv_self, Langlands.LinearAlgebra.cartan_D_det (by omega),
    Langlands.LinearAlgebra.cartan_A_det] at hd
  omega

/-- An absolutely almost-simple group of type D of rank at least four has
positive split rank over a nonarchimedean local field. -/
theorem TitsIndexData.not_isAnisotropic_of_typeD_local
    {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (habs : IsAbsolutelyAlmostSimple G) {n : ℕ} (hn : 4 ≤ n)
    (e : d.Vertex ≃ Fin n) (hD : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b)) :
    ¬ IsAnisotropic G := by
  intro h
  obtain ⟨m, _, f, hA⟩ := localAnisotropicTypeA K G d habs h
  refine not_typeA_of_typeD hn (e.symm.trans f) fun i j => ?_
  have ht := (hD (e.symm i) (e.symm j)).symm.trans (hA (e.symm i) (e.symm j))
  simpa only [Equiv.apply_symm_apply, Equiv.trans_apply] using ht

/-- Type D isotropy over any nonarchimedean local field extension of the
ground field, with the type specified by an actual index over that ground field. -/
def LocalTypeDIsotropyStatement : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G), IsAbsolutelyAlmostSimple G →
    ∀ (n : ℕ) (e : d.Vertex ≃ Fin n), 4 ≤ n →
      (∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b)) →
      ¬ IsAnisotropic ((GroupScheme.baseChange (algebraBaseMap F K)).obj G)

theorem localTypeDIsotropy : LocalTypeDIsotropyStatement.{u} := by
  intro F K _ _ _ _ _ _ G _ _ d hG n e hn hD
  let GK := (GroupScheme.baseChange (algebraBaseMap F K)).obj G
  have hGK : IsAbsolutelyAlmostSimple GK := hG.baseChange_field
  obtain ⟨dK⟩ := titsIndexExistence K GK hGK.1.isSemisimple
  obtain ⟨v, hv⟩ := d.exists_cartan_equiv_of_fieldExtension dK
  refine dK.not_isAnisotropic_of_typeD_local hGK hn (v.symm.trans e) fun a b => ?_
  obtain ⟨a, rfl⟩ := v.surjective a
  obtain ⟨b, rfl⟩ := v.surjective b
  simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using (hv a b).trans (hD a b)

end Langlands.GroupScheme
