import Langlands.GroupScheme.Reductive.GenericInnerIsomorphismTorsor
import Langlands.GroupScheme.Reductive.LocalIntegerIsomorphismStatement
import Langlands.GroupScheme.Reductive.GenericInnerIsomorphismTorsorExistenceStatement

/-! # Inner corrections obtained from an integral inner-isomorphism torsor -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open scoped ValuativeRel

namespace Langlands.GroupScheme

/-- The two actual adjoint quotients induce the same inner action under their
canonical comparison, even for points with no global lift. -/
theorem IsAdjointQuotient.innerAction_quotientIso
    {K : Type u} [Field K] {G A A' : GroupScheme (Spec (CommRingCat.of K))}
    {q : G ⟶ A} {q' : G ⟶ A'} (hq : IsAdjointQuotient q)
    (hq' : IsAdjointQuotient q') {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ A.X) (g : T ⟶ G.X) :
    hq'.innerAction.act (x ≫ (hq.quotientIso hq').hom.hom.hom) g =
      hq.innerAction.act x g := by
  let := hq.flat
  let := hq.surjective
  let := hq.isConnectedReductive.isAffineHom
  let := hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  apply AutomorphicAction.hom_ext_of_local_quotient_lift q x
  intro V t h ht
  rw [hq'.innerAction.naturality, hq.innerAction.naturality,
    ← Category.assoc, ht, Category.assoc]
  have he : q.hom.hom ≫ (hq.quotientIso hq').hom.hom.hom = q'.hom.hom :=
    congrArg (fun z => z.hom.hom) (hq.comp_quotientIso_hom hq')
  rw [he, hq'.innerAction_act_lift, hq.innerAction_act_lift]

/-- Projection of a constant generic point agrees with its forgotten-base family. -/
theorem baseChangePointsEquiv_basePoint_family
    {S S' : Scheme.{u}} (b : S' ⟶ S) (G : GroupScheme S)
    (x : Over.mk (𝟙 S') ⟶ ((baseChange b).obj G).X) (T : Over S') :
    baseChangePointsEquiv b G T
        ((Over.homMk T.hom : T ⟶ Over.mk (𝟙 S')) ≫ x) =
      LocalGroupIso.baseChangeTestPoint T ≫ baseChangeBasePointsEquiv b G x := by
  apply Over.OverMorphism.ext
  change (T.hom ≫ x.left) ≫ pullback.fst G.X.hom b =
    T.hom ≫ (baseChangeBasePointsEquiv b G x).left
  rw [baseChangeBasePointsEquiv_left, Category.assoc]

namespace GenericInnerIsomorphismTorsor

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  {f : (baseChange (Spec.algebraMap R K)).obj G ≅
    (baseChange (Spec.algebraMap R K)).obj H}
  (d : GenericInnerIsomorphismTorsor R K G H f)

/-- Any integral section gives the prescribed generic isomorphism after an
inner correction in the generic adjoint group. -/
theorem exists_correction_of_section
    (p : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ d.parameter) :
    ∃ (x : rationalPoints ((baseChange (Spec.algebraMap R K)).obj d.adjoint))
      (Φ : G ≅ H),
      ∀ (T : Over (Spec (CommRingCat.of K)))
        (g : T ⟶ ((baseChange (Spec.algebraMap R K)).obj G).X),
        g ≫ ((baseChange (Spec.algebraMap R K)).map Φ.hom).hom.hom =
          d.genericQuotient.innerAction.act
              ((Over.homMk T.hom : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≫ x) g ≫
            f.hom.hom.hom := by
  let b := Spec.algebraMap R K
  let pK : Over.mk b ⟶ d.parameter :=
    (Over.homMk b : Over.mk b ⟶ Over.mk (𝟙 _)) ≫ p
  let k := torsorDiff d.shear d.genericPoint pK
  let x := (baseChangeBasePointsEquiv b d.adjoint).symm k⁻¹
  refine ⟨x, d.localIso.atSection p, ?_⟩
  intro T g
  let t := LocalGroupIso.baseChangeTestPoint (U := Over.mk b) T
  let y : T ⟶ ((baseChange b).obj d.adjoint).X :=
    (Over.homMk T.hom : T ⟶ Over.mk (𝟙 _)) ≫ x
  have hx : baseChangePointsEquiv b d.adjoint T y = (t ≫ k)⁻¹ := by
    change baseChangePointsEquiv b d.adjoint T
      ((Over.homMk T.hom : T ⟶ Over.mk (𝟙 _)) ≫ x) = _
    rw [baseChangePointsEquiv_basePoint_family]
    change t ≫ baseChangeBasePointsEquiv b d.adjoint
      ((baseChangeBasePointsEquiv b d.adjoint).symm k⁻¹) = _
    rw [MulEquiv.apply_symm_apply, GrpObj.comp_inv]
  have hp : (t ≫ k) • (t ≫ d.genericPoint) =
      (Over.homMk ((Over.map b).obj T).hom :
        (Over.map b).obj T ⟶ Over.mk (𝟙 _)) ≫ p := by
    rw [← CategoryTheory.ModObj.comp_smul, torsorDiff_smul]
    apply Over.OverMorphism.ext
    change T.hom ≫ (b ≫ p.left) = (T.hom ≫ b) ≫ p.left
    exact (Category.assoc _ _ _).symm
  apply (baseChangePointsEquiv b H T).injective
  rw [baseChangePointsEquiv_comp, LocalGroupIso.comp_atSection_hom]
  rw [← hp, d.action_localIso]
  have hf := (d.localIso.refine d.genericPoint).toBaseChangeIso_hom_points T
    ((d.action.baseChange b).act y g)
  rw [d.genericIso, LocalGroupIso.refine_toFun] at hf
  change baseChangePointsEquiv b H T ((d.action.baseChange b).act y g ≫ f.hom.hom.hom) =
    d.localIso.toFun (t ≫ d.genericPoint)
      (baseChangePointsEquiv b G T ((d.action.baseChange b).act y g)) at hf
  rw [d.action.baseChangePointsEquiv_act, hx] at hf
  rw [← d.genericAction]
  exact hf.symm

/-- The correction works for any supplied actual generic adjoint quotient. -/
theorem exists_correction_for_quotient_of_section
    (p : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ d.parameter)
    (A : GroupScheme (Spec (CommRingCat.of K)))
    (q : (baseChange (Spec.algebraMap R K)).obj G ⟶ A)
    (hq : IsAdjointQuotient q) :
    ∃ (x : rationalPoints A) (Φ : G ≅ H),
      ∀ (T : Over (Spec (CommRingCat.of K)))
        (g : T ⟶ ((baseChange (Spec.algebraMap R K)).obj G).X),
        g ≫ ((baseChange (Spec.algebraMap R K)).map Φ.hom).hom.hom =
          hq.innerAction.act
              ((Over.homMk T.hom : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≫ x) g ≫
            f.hom.hom.hom := by
  obtain ⟨x, Φ, hΦ⟩ := d.exists_correction_of_section p
  refine ⟨x ≫ (d.genericQuotient.quotientIso hq).hom.hom.hom, Φ, ?_⟩
  intro T g
  simpa only [← Category.assoc,
    d.genericQuotient.innerAction_quotientIso hq] using hΦ T g

include d in
/-- Complete rings with finite residue trivialize the supplied torsor and
therefore supply the inner correction for every generic adjoint quotient. -/
theorem exists_correction
    (I : Ideal R) [I.IsMaximal] [Finite (R ⧸ I)] [IsAdicComplete I R]
    (A : GroupScheme (Spec (CommRingCat.of K)))
    (q : (baseChange (Spec.algebraMap R K)).obj G ⟶ A)
    (hq : IsAdjointQuotient q) :
    ∃ (x : rationalPoints A) (Φ : G ≅ H),
      ∀ (T : Over (Spec (CommRingCat.of K)))
        (g : T ⟶ ((baseChange (Spec.algebraMap R K)).obj G).X),
        g ≫ ((baseChange (Spec.algebraMap R K)).map Φ.hom).hom.hom =
          hq.innerAction.act
              ((Over.homMk T.hom : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≫ x) g ≫
            f.hom.hom.hom := by
  obtain ⟨p⟩ := d.nonempty_section I
  exact d.exists_correction_for_quotient_of_section p A q hq

end GenericInnerIsomorphismTorsor

/-- The remaining geometric existence theorem over general DVRs suffices for the
unchanged local-integer isomorphism statement. -/
theorem reductiveLocalIntegerIsomorphism_of_genericInnerIsomorphismTorsorExistence
    (h : GenericInnerIsomorphismTorsorExistenceStatement.{u}) :
    ReductiveLocalIntegerIsomorphismStatement.{u} := by
  intro F _ _ _ _ G H hG hH f A q hq
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  obtain ⟨d⟩ := h (↥𝒪[F]) F G H hG hH f
  exact d.exists_correction 𝓂[F] A q hq

end Langlands.GroupScheme
