import Langlands.GroupScheme.Torus.SelfCentralizingConjugacyValuationLiftStatement
import Langlands.GroupScheme.Torus.TorusGraphGroupQuotient
import Langlands.GroupScheme.Torus.ValuationIntegralFactor
import Langlands.GroupScheme.Torus.TorusImageFieldFibre
import Langlands.GroupScheme.Torus.SeparatedTransporter
import Langlands.GroupScheme.HomScheme.ConjugateFamilyProductLift
import Langlands.GroupScheme.Absolute.SolvableMaximalTorusSemidirectOfSection
import Langlands.GroupScheme.Reductive.TorusFibreMaximality
import Langlands.GroupScheme.Torus.RelativeHenselianSplitting
import Langlands.GroupScheme.Torus.RelativeReductive
import Langlands.GroupScheme.Torus.RelativeGeometry
import Langlands.GroupScheme.Torus.ConnectedQuotientCommutative
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.Galois.Local.SeparableHenselian
import Langlands.Galois.Local.SpectralProof

/-! # Valuative lifting for conjugates of the image torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ValuationLift

open TorusSubgroupModuli SubgroupFunctor

/-- Residue maximality, Henselian conjugacy and the smooth product lift: an integral
closed factor of the evaluated torus through the graph quotient, with an isomorphism
of generic sources, makes the valuation-ring point a value of the conjugacy map. -/
theorem exists_lift_of_integralFactor
    {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [Smooth G.X.hom]
    (hfib : ∀ s : Spec R,
      ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left ∧
        IsAffineHom (RelativeIdentityComponent.residueFiber G s).X.hom)
    {m : ℕ} (ρ : MatrixRepresentation G (Fin m))
    {T : CommGroupScheme (Spec R)} (t : T.toGrp ⟶ G) (hmax : IsFibrewiseMaximalTorus t)
    {D : CommGroupScheme (Spec R)} (π : T.toGrp ⟶ D.toGrp)
    (e : D.toGrp ⟶ GeneralLinear.groupScheme (Fin m) R)
    (hD : RelativeTorus.IsTorus D.toGrp) (he : IsClosedSubgroup e)
    (hπs : Surjective π.hom.hom.left) (hπe : π ≫ e = t ≫ ρ)
    (F : TorusGraphQuotient.GroupFactorization ρ e)
    {M : Over (Spec R)} {K : GroupScheme M.left}
    (j : K ⟶ (baseChange M.hom).obj (GeneralLinear.groupScheme (Fin m) R))
    (hj : IsClosedSubgroup j) (hK : RelativeTorus.IsTorus K) (huni : IsUniversal j)
    (f : G.X ⟶ M) (hf : evaluate j f = range (conjugateFamily e ρ.hom.hom))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω)
    (b : Spec (CommRingCat.of A) ⟶ M.left)
    (c : (baseChange b).obj K ⟶ (baseChange (b ≫ M.hom)).obj F.quotient)
    (hc : c ≫ (baseChange (b ≫ M.hom)).map F.embedding =
      familyHom j (Over.homMk b rfl : Over.mk (b ≫ M.hom) ⟶ M))
    (hcl : IsClosedSubgroup c)
    (σ : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap A Ω)))).obj
        ((baseChange b).obj K) ≅
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap A Ω)))).obj
        ((baseChange (b ≫ M.hom)).obj D.toGrp)) :
    ∃ h : Spec (CommRingCat.of A) ⟶ G.X.left, h ≫ f.left = b := by
  let : HenselianLocalRing A := Langlands.LocalGalois.Separable.sepClosed_henselian A
  let : IsAlgClosed (IsLocalRing.ResidueField A) := Langlands.LocalGalois.residue_isAlgClosed A
  have hk : Function.Surjective (algebraMap A (IsLocalRing.ResidueField A)) :=
    IsLocalRing.residue_surjective
  let : Smooth F.quotient.X.hom := F.smooth_quotient
  let : IsSeparated F.quotient.X.hom := F.separated_quotient
  let : QuasiCompact F.quotient.X.hom := F.quasiCompact_quotient
  let : Flat F.projection.hom.hom.left := F.flat_projection
  let : Surjective F.projection.hom.hom.left := F.surjective_projection
  let : Mono F.embedding.hom.hom.left := F.mono_embedding
  let : Smooth F.smoothCover.left := F.smooth_cover
  let : Surjective F.smoothCover.left := F.surjective_cover
  let : Surjective π.hom.hom.left := hπs
  let : Smooth (GeneralLinear.groupScheme (Fin m) R).X.hom :=
    GeneralLinear.smoothStatement (Fin m) R
  let : IsAffineHom (GeneralLinear.groupScheme (Fin m) R).X.hom := by
    change IsAffineHom (Spec.map _)
    infer_instance
  let : Smooth ((baseChange (b ≫ M.hom)).obj F.quotient).X.hom :=
    inferInstanceAs (Smooth (pullback.snd F.quotient.X.hom (b ≫ M.hom)))
  let : IsSeparated ((baseChange (b ≫ M.hom)).obj F.quotient).X.hom :=
    inferInstanceAs (IsSeparated (pullback.snd F.quotient.X.hom (b ≫ M.hom)))
  -- Residue fibre of the quotient: connected, affine, with maximal image torus.
  obtain ⟨hconn, haff, hdmax⟩ := torusImageMaximal_fieldPoint F.projection F.embedding
    (fun s => (hfib s).1) (fun s => (hfib s).2) t F.torus π hmax hD
    (F.isClosedSubgroup_torus he) (F.torus_comp t π hπe).symm
    (Spec.algebraMap A (IsLocalRing.ResidueField A) ≫ b ≫ M.hom)
  let φ := baseChangeCompIso' (b ≫ M.hom) (Spec.algebraMap A (IsLocalRing.ResidueField A))
    F.quotient
  let : ConnectedSpace ((baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj
      ((baseChange (b ≫ M.hom)).obj F.quotient)).X.left :=
    let ψ := (Over.forget _).mapIso ((Grp.forget _).mapIso φ)
    @Function.Surjective.connectedSpace _ _ _ hconn _ _
      (show Surjective ψ.hom from inferInstance).surj ψ.hom.continuous
  let : IsAffineHom ((baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj
      ((baseChange (b ≫ M.hom)).obj F.quotient)).X.hom := by
    rw [← Over.w φ.inv.hom.hom]
    infer_instance
  let : Smooth ((baseChange (Spec.algebraMap A (IsLocalRing.ResidueField A))).obj
      ((baseChange (b ≫ M.hom)).obj F.quotient)).X.hom :=
    inferInstanceAs (Smooth (pullback.snd ((baseChange (b ≫ M.hom)).obj F.quotient).X.hom
      (Spec.algebraMap A (IsLocalRing.ResidueField A))))
  have hdmax' := isMaximalTorus_baseChange_comp (b ≫ M.hom)
    (Spec.algebraMap A (IsLocalRing.ResidueField A)) D F.torus hdmax
  -- Both integral tori split over the strictly Henselian valuation ring.
  have hDA : IsSplitTorus ((CommGroupScheme.baseChange (b ≫ M.hom)).obj D).toGrp :=
    (hD.baseChange (b ≫ M.hom)).isSplitTorus_of_henselian hk
  have hB : IsSplitTorus ((baseChange b).obj K) :=
    (hK.baseChange b).isSplitTorus_of_henselian hk
  have hcmax := isMaximalTorus_fieldFibre_of_split_of_fieldIso
    (Spec.map (CommRingCat.ofHom (algebraMap A Ω)))
    (Spec.algebraMap A (IsLocalRing.ResidueField A))
    (Q := (baseChange (b ≫ M.hom)).obj F.quotient)
    (D := (CommGroupScheme.baseChange (b ≫ M.hom)).obj D) (B := hB.toCommGroupScheme)
    hDA hB (d := (baseChange (b ≫ M.hom)).map F.torus) c hcl hdmax' σ.symm
  -- Integral conjugacy in the separated quotient, then the smooth product lift.
  obtain ⟨z, ε, hz⟩ := exists_henselian_splitTorus_conjugacy_of_separated
    (G := (baseChange (b ≫ M.hom)).obj F.quotient)
    (T₁ := (CommGroupScheme.baseChange (b ≫ M.hom)).obj D) (T₂ := hB.toCommGroupScheme)
    ((baseChange (b ≫ M.hom)).map F.torus) c hDA hB hk hdmax' hcmax
  have hrange := evaluate_eq_range_conjugatePullback_of_factor (b ≫ M.hom) F.embedding F.torus j
    (Over.homMk b rfl : Over.mk (b ≫ M.hom) ⟶ M) c hc z (CommGroupScheme.groupIso ε) hz
  rw [F.torus_fac] at hrange
  obtain ⟨h, hh⟩ := exists_parameter_of_conjugate_of_smooth_product (b ≫ M.hom) ρ e F.embedding
    F.smoothCover F.cover_fac j hj hK huni f hf (Over.homMk b rfl) z hrange
  exact ⟨h.left, congrArg CommaMorphism.left hh⟩

end Langlands.GroupScheme.ValuationLift

namespace Langlands.GroupScheme

open TorusSubgroupModuli SubgroupFunctor

/-- **Valuative lifting for the conjugacy map to the subtori of `GL_m`.** Over a
valuation subring `A` of an algebraically closed field, a point of the scheme of
subtori whose generic point is a value of the conjugacy map is itself a value of it. -/
theorem selfCentralizingConjugacyValuationLift :
    SelfCentralizingConjugacyValuationLiftStatement.{u} := by
  intro R G hGsm hGsep hGqc hfib m ρ hρ T t hT ht hmax hcent D π e hD he hπf hπs hπl hπe
    M K j hj hK huni f hf Ω _ _ A g b hgb
  let : Smooth G.X.hom := hGsm
  let : QuasiCompact G.X.hom := hGqc
  let : Flat π.hom.hom.left := hπf
  let : Surjective π.hom.hom.left := hπs
  let : LocallyOfFinitePresentation π.hom.hom.left := hπl
  let : Smooth D.X.hom := hD.smooth
  let : QuasiCompact D.X.hom := by
    have := hD.isAffineHom
    infer_instance
  let : IsSeparated (GeneralLinear.groupScheme (Fin m) R).X.hom := by
    change IsSeparated (Spec.map _)
    infer_instance
  let : QuasiSeparated (GeneralLinear.groupScheme (Fin m) R).X.hom := by
    change QuasiSeparated (Spec.map _)
    infer_instance
  have heMono : Mono e.hom.hom := by
    have : IsClosedImmersion e.hom.hom.left := he
    exact Over.mono_of_mono_left _
  let F := TorusGraphQuotient.groupFactorization ρ t π e hρ hcent heMono hπe hT.smooth
  let I := F.integralFactor A he j hj hK f hf g b hgb
  exact ValuationLift.exists_lift_of_integralFactor hfib ρ t hmax π e hD he hπs hπe F j hj hK
    huni f hf A b I.factor I.fac I.isClosedSubgroup_factor I.genericIso

end Langlands.GroupScheme
