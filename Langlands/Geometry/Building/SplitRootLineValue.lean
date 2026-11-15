import Langlands.Geometry.Building.SplitApartmentGaloisFixedPoint
import Langlands.GroupScheme.Rational.RootPointLieNaturality
import Langlands.GroupScheme.Rational.RootFieldVectorIso
import Langlands.GroupScheme.SplitExistence.RootSubgroupRepresentation
import Langlands.GroupScheme.Rational.MonicRootParametrization
import Langlands.GroupScheme.Rational.CrossTorusLieTransport

/-! # Values of split apartment points along actual root lines -/

noncomputable section



universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.VectorGroup

namespace IsTorusEquivariant

open Langlands.GroupScheme.SplitExistence.ChevalleyData

variable {k : Type u} [Field k]

section Transport

variable {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}

/-- Torus equivariance of an additive line is carried backwards along a
commuting square of torus and ambient group isomorphisms. -/
theorem transport (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    {x : groupScheme (CommRingCat.of k) 1 ⟶ H} {a : characterLattice S'}
    (hx : IsTorusEquivariant j x a) :
    IsTorusEquivariant i (x ≫ f.inv) (e.hom ≫ a) := by
  intro Z t c
  have hi : i = CommGroupScheme.groupHom e.hom ≫ j ≫ f.inv := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have ht : t ≫ i.hom.hom =
      ((t ≫ (CommGroupScheme.groupHom e.hom).hom.hom) ≫ j.hom.hom) ≫ f.inv.hom.hom := by
    rw [hi, Grp.comp_hom_hom, Grp.comp_hom_hom]
    simp only [Category.assoc]
  have hval : charValue (e.hom ≫ a) Z t =
      charValue a Z (t ≫ (CommGroupScheme.groupHom e.hom).hom.hom) := by
    unfold charValue
    rw [comp_groupHom_comp]
  have hc : ∀ c', scalarPoint (CommRingCat.of k) Z c' ≫ (x ≫ f.inv).hom.hom =
      (scalarPoint (CommRingCat.of k) Z c' ≫ x.hom.hom) ≫ f.inv.hom.hom := fun _ => by
    rw [Grp.comp_hom_hom, Category.assoc]
  have he := congrArg (fun q => q ≫ f.inv.hom.hom)
    (hx Z (t ≫ (CommGroupScheme.groupHom e.hom).hom.hom) c)
  simp only [MonObj.mul_comp, GrpObj.inv_comp] at he
  rw [ht, hval, hc, hc, ← he]

end Transport

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G}
    {x : groupScheme (CommRingCat.of k) 1 ⟶ G} {α : characterLattice T}

/-- The natural additive coordinate of a representing equivariant line is a
weight coordinate for the actual torus action on the representative. -/
theorem isWeightVectorCoordinates_subgroupAction (hx : IsTorusEquivariant i x α)
    (hrep : (RelativeRoot.subgroup i α).IsRepresentedBy x) :
    RelativeRoot.IsWeightVectorCoordinates (RelativeRoot.subgroupAction i α x hrep) α
      (coordinates (CommRingCat.of k) 1) := by
  refine ⟨isNaturalVectorCoordinates, fun Z s v => ?_⟩
  have : Mono x.hom.hom := hrep.1
  have hact : (RelativeRoot.subgroupAction i α x hrep).act s v = (weightAction α).act s v := by
    apply (cancel_mono x.hom.hom).mp
    rw [RelativeRoot.subgroupAction_act_comp, hx.weightAction_comp,
      AutomorphicAction.conjugation_act]
  rw [hact]
  exact coordinates_weightAction_act α s v

local instance : IsAffineHom (groupScheme (CommRingCat.of k) 1).X.hom :=
  isAffineHom_groupScheme (CommRingCat.of k) 1

/-- The vector-group point-to-Lie comparison is linear along the field
coordinate of `𝔾ₐ`. -/
theorem vectorPointLieEquiv_gaRationalEquiv (s : CommAlgCat.of k k) :
    RelativeRoot.vectorPointLieEquiv (coordinates (CommRingCat.of k) 1)
        isNaturalVectorCoordinates (CommAlgCat.of k k)
        (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k _
          (gaRationalEquiv k (Multiplicative.ofAdd s)))) =
      s • RelativeRoot.vectorPointLieEquiv
        (coordinates (CommRingCat.of k) 1)
        isNaturalVectorCoordinates (CommAlgCat.of k k)
        (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k _
          (gaRationalEquiv k (Multiplicative.ofAdd 1)))) := by
  apply (RelativeRoot.vectorLieCoordinates (coordinates (CommRingCat.of k) 1)
    isNaturalVectorCoordinates (CommAlgCat.of k k)).injective
  rw [map_smul, RelativeRoot.vectorLieCoordinates_vectorPointLieEquiv,
    RelativeRoot.vectorLieCoordinates_vectorPointLieEquiv, toMul_ofMul, toMul_ofMul,
    RelativeRoot.vectorAffineCoordinates_rationalCoeffEquiv _ isNaturalVectorCoordinates,
    RelativeRoot.vectorAffineCoordinates_rationalCoeffEquiv _ isNaturalVectorCoordinates]
  funext l
  rw [Pi.smul_apply, Langlands.Geometry.Building.ChevalleyRootFamily.gaRationalEquiv_eq_scalarPoint,
    Langlands.Geometry.Building.ChevalleyRootFamily.gaRationalEquiv_eq_scalarPoint,
    coordinates_scalarPoint, coordinates_scalarPoint, smul_eq_mul, map_one, map_one, mul_one]
  exact (Scheme.ΓSpecIso (CommRingCat.of k)).inv_hom_id_apply s

variable [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- **Linearity of intrinsic root coordinates along an equivariant line.**
The intrinsic point-to-Lie comparison sends the point with field coordinate
`s` of a representing torus-equivariant additive line to `s` times the image
of the point with coordinate `1`. -/
theorem rootPointLieEquiv_smul (hS : IsSplitTorus T.toGrp) (ha : α ≠ 0)
    (hhigh : RelativeRoot.HasNoHigherRoots i α) (hx : IsTorusEquivariant i x α)
    (hrep : (RelativeRoot.subgroup i α).IsRepresentedBy x) (s : CommRingCat.of k) :
    RelativeRoot.rootPointLieEquiv hS i ha hhigh
        (Additive.ofMul (hrep.pointsEquiv _ (gaRationalEquiv k (Multiplicative.ofAdd s)))) =
      s • RelativeRoot.rootPointLieEquiv hS i ha hhigh
        (Additive.ofMul (hrep.pointsEquiv _ (gaRationalEquiv k (Multiplicative.ofAdd 1)))) := by
  have hw := isWeightVectorCoordinates_subgroupAction hx hrep
  let c := RelativeRoot.weightVectorCoordinatesOfNoHigherRoots hS i ha hhigh hrep
  have heq := RelativeRoot.vectorPointLieEquiv_eq_of_weight hS ha c.2.property hw
    (CommAlgCat.of k k)
  have key : ∀ v, (RelativeRoot.representedRootPointLieEquiv hS i ha hhigh hrep
      (Additive.ofMul (hrep.pointsEquiv _ v)) : Additive (lieKernel G k)) =
      Lie.targetMapLinear x k (RelativeRoot.vectorPointLieEquiv
        (coordinates (CommRingCat.of k) 1) isNaturalVectorCoordinates (CommAlgCat.of k k)
        (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k _ v))) := by
    intro v
    have h := RelativeRoot.representedRootPointLieEquiv_apply hS i ha hhigh hrep v
    exact h.trans (by rw [heq])
  apply Subtype.ext
  rw [RelativeRoot.rootPointLieEquiv_eq_represented hS i ha hhigh hrep, Submodule.coe_smul,
    key, key, vectorPointLieEquiv_gaRationalEquiv]
  exact (Lie.targetMapLinear x k).map_smul s _

end IsTorusEquivariant

end Langlands.GroupScheme.VectorGroup

namespace Langlands.Geometry.Building

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.SplitExistence Langlands.GroupScheme.SplitExistence.ChevalleyData

variable {k : Type u} [Field k]

/-- **Split apartments along a Chevalley root parametrization.** For a split maximal torus of
a connected reductive group and any normalizer-stable apartment class, every relative root
has a monic torus-equivariant additive line along which every point of the class is the
field valuation of the additive coordinate plus a constant. The line is the transport of the
Chevalley root homomorphism through the split isomorphism with the Chevalley group. -/
theorem exists_rootParametrization_value_of_isSplitTorus
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) [Mono j.hom.hom.left] (hj : IsMaximalTorus j)
    (omega : AddValuation k (WithTop ℝ)) (ω : kˣ → ℝ)
    (hω : ∀ x : kˣ, omega (x : k) = ((ω x : ℝ) : WithTop ℝ))
    (h3 : 3 ≤ (Set.range omega).encard) (A : KPApartmentData j ω)
    {α : characterLattice T} (hα : α ∈ relativeRoots j) :
    ∃ x : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G,
      VectorGroup.IsTorusEquivariant j x α ∧ Mono x.hom.hom ∧
      ∀ φ ∈ A.carrier, ∃ c : ℝ, ∀ s : k,
        φ α (gaRationalEquiv k (Multiplicative.ofAdd s) ≫ x.hom.hom) =
          omega s + ((c : ℝ) : WithTop ℝ) := by
  classical
  have hadd (s t : kˣ) : ω (s * t) = ω s + ω t := by
    have he := omega.map_mul (s : k) (t : k)
    rw [← Units.val_mul, hω, hω, hω, ← WithTop.coe_add, WithTop.coe_inj] at he
    exact he
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence k G hG T hT j hj
  have : Module.Finite ℤ (characterLattice T) := hT.finite_characterLattice
  have := isTorsionFree_weight P
  obtain ⟨b⟩ := nonempty_base_int P
  obtain ⟨DL⟩ := nonempty_chevalleyLieData P b
  let D : ChevalleyData P b := DL.toChevalleyData
  obtain ⟨Gc⟩ := D.nonempty_chevGroup k
  have : IsAffineHom Gc.H.X.hom := Gc.affine
  have : IsAffine Gc.H.X.left := isAffine_of_isAffineHom Gc.H.X.hom
  have : Smooth Gc.H.X.hom := Gc.smooth
  have hGcmax : IsMaximalTorus Gc.t := Gc.isMaximalTorus
  have : IsClosedImmersion Gc.t.hom.hom.left := hGcmax.2.1
  let Dc := ChevalleyRootFamily.apartmentData Gc omega ω hω h3
  let t : T ≅ Tk (X := characterLattice T) k :=
    hT.isoOfCharacterEquiv (isSplitTorus_Tk k P) (charEquiv k (X := characterLattice T))
  have hR : IsRootDatumOf (CommGroupScheme.groupHom t.hom ≫ Gc.t) P :=
    IsRootDatumOf.precomp_torusIso t Gc.isRootDatumOf hP.1 (chevDatumEquiv k P) fun χ => by
      rw [hT.character_congr_isoOfCharacterEquiv (isSplitTorus_Tk k P)]
      rfl
  have hM : IsMaximalTorus (CommGroupScheme.groupHom t.hom ≫ Gc.t) :=
    IsMaximalTorus.precomp_torusIso t hGcmax
  obtain ⟨ψ, hψ⟩ := splitCommonTorusIsomorphism k G Gc.H hG Gc.isConnectedReductive T hT j
    (CommGroupScheme.groupHom t.hom ≫ Gc.t) hj hM J J P P hP hR (Equiv.refl J) rfl rfl
  have hA : A = Dc.transport t.symm ψ.symm (torusTransport_inverse_square t ψ hψ) :=
    KPApartmentData.eq_of_isMaximalTorus_of_isSplitTorus hG hT hj hadd _ _
  have hα' : characterLattice.congr t α ∈ relativeRoots Gc.t := by
    rw [← relativeRoots_image_of_transport t ψ hψ]
    exact ⟨α, hα, rfl⟩
  obtain ⟨j0, hj0⟩ := (ChevalleyRootFamily.mem_relativeRoots_iff Gc _).1 hα'
  refine ⟨Gc.u j0 ≫ ψ.inv, ?_, ?_, ?_⟩
  · have h := (Gc.u_isTorusEquivariant j0).transport t ψ hψ
    have hc : t.hom ≫ charOf k (P.root j0) = α := by
      rw [hj0]
      exact Iso.hom_inv_id_assoc t α
    rwa [hc] at h
  · change Mono ((Gc.u j0).hom.hom ≫ ψ.inv.hom.hom)
    infer_instance
  · intro φ hφ
    rw [hA, KPApartmentData.transport_carrier] at hφ
    obtain ⟨φc, hφc, rfl⟩ := hφ
    obtain ⟨v, rfl⟩ := hφc
    refine ⟨eval _ (charOf k (P.root j0)) v, fun s => ?_⟩
    have hchar : (characterLattice.congr t.symm).symm α = charOf k (P.root j0) := by
      rw [hj0]
      rfl
    have hpt : rationalPoints.map ψ.symm.inv
        (gaRationalEquiv k (Multiplicative.ofAdd s) ≫ (Gc.u j0 ≫ ψ.inv).hom.hom) =
        (ChevalleyRootFamily.rootCoord Gc j0 (Multiplicative.ofAdd s) :
          rationalPoints Gc.H) := by
      rw [rationalPoints.map_apply, ChevalleyRootFamily.rootCoord_apply_coe, Iso.symm_inv,
        Grp.comp_hom_hom, Category.assoc, Category.assoc, ← Grp.comp_hom_hom ψ.inv ψ.hom,
        Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
    rw [RootFunctionFamily.transportEquiv_apply, hchar, hpt, RootFunctionFamily.vadd_apply,
      ChevalleyRootFamily.family_root, additiveRootValue_coordinate]

/-- **Root-line points.** For a nonzero relative root `α` of a split torus without higher
roots and a `k`-linear identification `ℓ` of `k` with the weight space of `α`, the actual
`k`-rational point of the root subgroup of `α` whose intrinsic Lie coordinate
(`RelativeRoot.rootPointLieEquiv`) is `ℓ w`, regarded as a rational point of `G`. -/
def rootLinePoint {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [Smooth G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G) {α : characterLattice T} (ha : α ≠ 0)
    (hhigh : RelativeRoot.HasNoHigherRoots j α) (ℓ : k ≃ₗ[k] weightSpace j α) (w : k) :
    rationalPoints G :=
  ((RelativeRoot.rootPointLieEquiv hT j ha hhigh).symm (ℓ w)).toMul.val

/-- The root-line point lies in the actual root subgroup. -/
theorem rootLinePoint_mem {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [Smooth G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G) {α : characterLattice T} (ha : α ≠ 0)
    (hhigh : RelativeRoot.HasNoHigherRoots j α) (ℓ : k ≃ₗ[k] weightSpace j α) (w : k) :
    rootLinePoint hT j ha hhigh ℓ w ∈ (RelativeRoot.subgroup j α).carrier (Over.mk (𝟙 _)) :=
  ((RelativeRoot.rootPointLieEquiv hT j ha hhigh).symm (ℓ w)).toMul.property

/-- **Values of split apartment points on actual root lines.** Let `j` be a split maximal
torus of a connected reductive group, `A` any normalizer-stable apartment class and `φ` a
point of `A`. For a relative root `α` without higher multiples and any `k`-linear
identification `ℓ` of `k` with the weight space of `α`, the value of `φ` at the root-line
point `rootLinePoint hT j ha hhigh ℓ w` is the valuation of `w` plus a constant
independent of `w`. -/
theorem exists_rootLine_value_of_isSplitTorus
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) [Mono j.hom.hom.left] (hj : IsMaximalTorus j)
    (omega : AddValuation k (WithTop ℝ)) (ω : kˣ → ℝ)
    (hω : ∀ x : kˣ, omega (x : k) = ((ω x : ℝ) : WithTop ℝ))
    (h3 : 3 ≤ (Set.range omega).encard) (A : KPApartmentData j ω)
    {α : characterLattice T} (hα : α ∈ relativeRoots j) (ha : α ≠ 0)
    (hhigh : RelativeRoot.HasNoHigherRoots j α)
    (ℓ : k ≃ₗ[k] weightSpace j α) {φ : RootFunctionFamily T G} (hφ : φ ∈ A.carrier) :
    ∃ c : ℝ, ∀ w : k,
      φ α (rootLinePoint hT j ha hhigh ℓ w) = omega w + ((c : ℝ) : WithTop ℝ) := by
  obtain ⟨x, hx, hmono, hval⟩ :=
    exists_rootParametrization_value_of_isSplitTorus G hG T hT j hj omega ω hω h3 A hα
  obtain ⟨c, hc⟩ := hval φ hφ
  have hrep := hx.represents_root hG hT hj hα hhigh
  let R := RelativeRoot.rootPointLieEquiv hT j ha hhigh
  let p : k → (RelativeRoot.subgroup j α).carrier (Over.mk (𝟙 _)) := fun s =>
    hrep.pointsEquiv _ (gaRationalEquiv k (Multiplicative.ofAdd s))
  have hlin (s : CommRingCat.of k) :
      R (Additive.ofMul (p s)) = s • R (Additive.ofMul (p 1)) :=
    VectorGroup.IsTorusEquivariant.rootPointLieEquiv_smul hT ha hhigh hx hrep s
  have hp_inj : Function.Injective p := fun s t h =>
    Multiplicative.ofAdd.injective ((gaRationalEquiv k).injective
      ((hrep.pointsEquiv _).injective h))
  have hp0 : p 0 = 1 := by
    change hrep.pointsEquiv _ (gaRationalEquiv k (Multiplicative.ofAdd 0)) = 1
    rw [ofAdd_zero, map_one, map_one]
  have hp1 : R (Additive.ofMul (p 1)) ≠ 0 := by
    intro h0
    have h : Additive.ofMul (p 1) = Additive.ofMul (p 0) := by
      apply R.injective
      rw [h0, hp0]
      exact R.map_zero.symm
    exact one_ne_zero (hp_inj (Additive.ofMul.injective h))
  let m : k := ℓ.symm (R (Additive.ofMul (p 1)))
  have hm' : ℓ m = R (Additive.ofMul (p 1)) := ℓ.apply_symm_apply _
  have hm : m ≠ 0 := by
    intro h
    apply hp1
    rw [← hm', h, map_zero]
  have key (w : k) : R.symm (ℓ w) = Additive.ofMul (p (w * m⁻¹)) := by
    apply R.injective
    rw [R.apply_symm_apply, hlin]
    calc ℓ w = ℓ ((w * m⁻¹) • m) := by rw [smul_eq_mul, inv_mul_cancel_right₀ hm]
      _ = (w * m⁻¹) • ℓ m := map_smul ℓ _ _
      _ = _ := by rw [hm']
  refine ⟨ω (Units.mk0 m⁻¹ (inv_ne_zero hm)) + c, fun w => ?_⟩
  change φ α ((R.symm (ℓ w)).toMul.val) = _
  rw [key w, toMul_ofMul]
  change φ α ((hrep.pointsEquiv _ (gaRationalEquiv k (Multiplicative.ofAdd (w * m⁻¹))) :
    rationalPoints G)) = _
  have hv : omega m⁻¹ = ((ω (Units.mk0 m⁻¹ (inv_ne_zero hm)) : ℝ) : WithTop ℝ) :=
    hω (Units.mk0 m⁻¹ (inv_ne_zero hm))
  rw [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe, hc, AddValuation.map_mul, hv,
    WithTop.coe_add, add_assoc]

end Langlands.Geometry.Building
