import Langlands.GroupScheme.Derived.Functoriality
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Derived.SemisimpleProof
import Langlands.GroupScheme.Rational.QuadraticCocharacterCentralizerDescent
import Langlands.GroupScheme.Rational.QuadraticSplitMaximalTorus
import Langlands.GroupScheme.Rational.TypeE6ParabolicDimensions
import Langlands.GroupScheme.Reductive.GeometricSimplyConnected
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Langlands.GroupScheme.Reductive.StandardLeviDerivedPinning
import Langlands.GroupScheme.Reductive.TitsIndexFieldExtensionCartan

/-! # An actual type A2 subgroup in the anisotropic quadratic splitting argument for E6 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 100000

private local instance affineBaseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [IsAffineHom G.X.hom] : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›

private def omittedVertices : Finset (Fin 6) := {1, 3, 4, 5}

private def typeA2FaceEquiv : Fin 2 ≃ {a : Fin 6 // a ∉ omittedVertices} :=
  Equiv.ofBijective
    (fun i => if i = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩) (by decide)

private theorem typeA2Face_cartan (a b : Fin 2) :
    CartanMatrix.E 6 (typeA2FaceEquiv a).val (typeA2FaceEquiv b).val =
      CartanMatrix.A 2 a b := by
  fin_cases a <;> fin_cases b <;> decide

/-- An anisotropic simply connected E6 form split by a quadratic Galois
extension has a simply connected closed subgroup whose base change to
that extension is split of type A2. -/
theorem IsAnisotropic.exists_quadraticSplit_typeA2_subgroup
    {k K : Type u} [Field k] [Infinite k] [Field K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (hG : IsAnisotropic G)
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6) (hsc : IsSimplyConnected G)
    (hcart : ∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b))
    (hK : Module.finrank k K = 2)
    (hsplit : HasSplitMaximalTorus ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)) :
    ∃ (D : GroupScheme (Spec (CommRingCat.of k))) (u : D ⟶ G) (hu : IsClosedSubgroup u),
      haveI := hu.isAffineHom
      IsSimplyConnected D ∧
        ∃ (q : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj D))
          (f : q.base.support ≃ Fin 2),
          ∀ a b, q.rootDatum.pairing a.val b.val = CartanMatrix.A 2 (f a) (f b) := by
  let b := algebraBaseMap k K
  let BC := GroupScheme.baseChange b
  let GK := BC.obj G
  let ψ : K →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let : Algebra K (SeparableClosure k) := ψ.toRingHom.toAlgebra
  let : IsScalarTower k K (SeparableClosure k) :=
    IsScalarTower.of_algebraMap_eq fun x => (ψ.commutes x).symm
  let : LocallyOfFiniteType GK.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom b))
  let : IsAffine GK.X.left := isAffine_of_isAffineHom GK.X.hom
  have hGK := connectedReductiveFieldExtensionStatement k K G hsc.isSemisimple.isConnectedReductive
  have hscK := isSimplyConnectedFieldExtension k K G hsc
  obtain ⟨T, t, ht, hT⟩ := quadraticSplitMaximalTorus k K hK G hsc.isSemisimple.isConnectedReductive hsplit
  let TK := (CommGroupScheme.baseChange b).obj T
  let tK : TK.toGrp ⟶ GK := BC.map t
  let : Smooth G.X.hom := hsc.isSemisimple.isConnectedReductive.smooth
  have htK := (maximalTorusBaseChange k K G T t ht.1 ht.2.1).mp ht
  obtain ⟨J, _, P, hP, hred⟩ := rootDatumExistence K GK hGK TK hT tK htK
  let base := d.splitMaximalTorusBase hT htK hP
  let p : SplitPinning GK :=
    { isConnectedReductive := hGK
      torus := TK
      inclusion := tK
      isSplitTorus := hT
      isMaximalTorus := htK
      rootIndex := J
      rootDatum := P
      isRootDatum := hP
      isReduced := hred
      base := base
      pinning := RootPinning.ofSplitMaximalTorus hGK hT tK htK P hP base }
  let η := d.splitMaximalTorusBaseEquiv hT htK hP
  let eK : p.base.support ≃ Fin 6 := η.symm.trans e
  have hcartK (x y : p.base.support) :
      p.rootDatum.pairing x.val y.val = CartanMatrix.E 6 (eK x) (eK y) := by
    obtain ⟨x, rfl⟩ := η.surjective x
    obtain ⟨y, rfl⟩ := η.surjective y
    have h := d.cartanMatrix_splitMaximalTorusBaseEquiv hT htK hP x y
    change base.cartanMatrix (η x) (η y) = d.cartan x y at h
    have h' : P.pairing (η x).val (η y).val = d.cartan x y :=
      (P.algebraMap_pairingIn ℤ (η x).val (η y).val).symm.trans h
    change P.pairing (η x).val (η y).val =
      CartanMatrix.E 6 (e (η.symm (η x))) (e (η.symm (η y)))
    rw [η.symm_apply_apply, η.symm_apply_apply]
    exact h'.trans (hcart x y)
  obtain ⟨_, hparabolic⟩ := typeE6ParabolicDimensions K GK p hscK eK hcartK
  obtain ⟨ν, hν, _⟩ := hparabolic omittedVertices
  let χ := CommGroupScheme.groupHom ν ≫ tK
  let M := Dynamic.Affine.centralizerScheme χ
  let m := Dynamic.Affine.centralizerHom χ
  let hm := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  obtain ⟨H, h, z, hh, -⟩ :=
    hG.exists_quadratic_cocharacterCentralizer_descent ht.2.1 ht.1 hT hK ν
  let hM := splitTorusCentralizerReductive K GK hGK (Gm _) χ isSplitTorus_gm M m
    ((torusCentralizer_gm_eq_dynamicCentralizer χ).symm ▸ hm)
  let hH := IsConnectedReductive.of_fieldExtension (K := K) (hM.of_iso z)
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : Smooth H.X.hom := hH.smooth
  obtain ⟨D, j, _, _, hj⟩ := derivedSubgroupRepresentability k H
  let jK := BC.map j ≫ z.hom
  have hD_K : IsDerivedSubgroup jK := by
    let hjK := hj.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b H)
    refine ⟨hjK.1.comp_iso z, ?_⟩
    dsimp only [jK]
    rw [SubgroupFunctor.range_comp_iso, hjK.2]
    exact derivedSubgroup_comap_iso z.symm
  have hνnonneg (a : p.base.support) : 0 ≤ p.rootDatum.root' a.val ν := by
    rw [hν]
    split <;> decide
  let : LocallyOfFiniteType (BC.obj D).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd D.X.hom b))
  obtain ⟨⟨Q⟩, hscD_K⟩ := p.standardLeviDerivedPinning ν hνnonneg m hm jK hD_K
  have hscD := (isSimplyConnected_fieldExtension_iff (K := K) D).mp (hscD_K hscK)
  let E : Q.pinning.base.support ≃ {a : Fin 6 // a ∉ omittedVertices} :=
    Q.vertices.trans (eK.subtypeEquiv (fun a => by
      rw [hν]
      by_cases ha : eK a ∈ omittedVertices <;> simp [ha]))
  let f : Q.pinning.base.support ≃ Fin 2 := E.trans typeA2FaceEquiv.symm
  refine ⟨D, j ≫ h, hj.1.comp hh, hscD, Q.pinning, f, fun a c => ?_⟩
  have hf (a : Q.pinning.base.support) : (typeA2FaceEquiv (f a)).val = eK (Q.vertices a).val :=
    congrArg Subtype.val (typeA2FaceEquiv.apply_symm_apply (E a))
  rw [Q.cartan_eq, hcartK, ← hf a, ← hf c, typeA2Face_cartan]

/-- An actual type A2 subgroup split over the same quadratic extension. -/
def TypeE6QuadraticSplitTypeA2Statement : Prop :=
  ∀ (k K : Type u) [Field k] [Infinite k] [Field K] [Algebra k K] [FiniteDimensional k K]
      [IsGalois k K], Module.finrank k K = 2 →
    ∀ (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom], IsAnisotropic G →
      ∀ (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6), IsSimplyConnected G →
        (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
        HasSplitMaximalTorus ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) →
        ∃ (D : GroupScheme (Spec (CommRingCat.of k))) (j : D ⟶ G) (hj : IsClosedSubgroup j),
          haveI := hj.isAffineHom
          IsSimplyConnected D ∧
            ∃ (q : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj D))
              (f : q.base.support ≃ Fin 2),
              ∀ a b, q.rootDatum.pairing a.val b.val = CartanMatrix.A 2 (f a) (f b)

theorem typeE6QuadraticSplitTypeA2 : TypeE6QuadraticSplitTypeA2Statement.{u} := by
  intro k K _ _ _ _ _ _ hK G _ _ hG d e hsc hcart hsplit
  exact hG.exists_quadraticSplit_typeA2_subgroup d e hsc hcart hK hsplit

end Langlands.GroupScheme
