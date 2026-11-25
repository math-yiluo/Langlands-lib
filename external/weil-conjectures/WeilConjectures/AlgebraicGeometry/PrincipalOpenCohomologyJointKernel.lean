/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietorisConnectingPullback
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial

/-! # Joint kernel of restrictions in a principal two-open cover

Source: Stacks Project, Tags 0GY0 and 0A50.
(blueprint: lem-weil-pbc-principal-open-cohomology-joint-kernel) -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Etale

private theorem cohomologyMap_joint_zero {X : Scheme.{u}} (U V : X.Opens)
    (hcover : U ⊔ V = ⊤)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (hprev : Subsingleton (Sheaf.H (((U ⊓ V).ι)^*[AddCommGrpCat.{u + 1}].obj F) n))
    (x : Sheaf.H F (n + 1))
    (hU : cohomologyMap U.ι F (n + 1) x = 0)
    (hV : cohomologyMap V.ι F (n + 1) x = 0) : x = 0 := by
  obtain ⟨δ, _, _, hex, _⟩ :=
    etale_mayerVietoris_connecting_pullback (𝟙 X) U V hcover F
  obtain ⟨y, hy⟩ := ((hex n).2.2 x).mp (Prod.ext hU hV)
  rw [hprev.elim y 0, map_zero] at hy
  exact hy.symm

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the two principal members of the cover has zero joint kernel
when the preceding cohomology group of their intersection vanishes.

Source: Stacks Project, Tag 0GY0, the displayed Mayer--Vietoris exact segment;
Tag 0A50, Mayer--Vietoris for etale cohomology.
(blueprint: lem-weil-pbc-principal-open-cohomology-joint-kernel)

Proof: Put W = D(a+b), U = W ∩ D(a), and V = W ∩ D(b). A prime avoiding
 a+b cannot contain both a and b, so U and V cover W. Their intersection is
 D(ab(a+b)). Apply the etale Mayer--Vietoris exact segment in degrees n and
 n+1 on W with coefficients F restricted to W. The inverse-image composition
 isomorphisms identify the intersection coefficients with F restricted to
 D(ab(a+b)), and the two outgoing maps with the displayed cohomologyMap maps.
 Every class killed by both maps is the image of an intersection class by
 exactness. The intersection group is subsingleton, so that class is zero;
 the additive connecting map sends it to zero. Thus x = 0. The argument also
 applies for n = 0, an empty W, a zero element, and repeated cover members. -/
theorem principalOpenCohomology_joint_kernel
    (R : Type u) [CommRing R]
    (F : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (a b : R) (n : ℕ)
    (hprev : Subsingleton (Sheaf.H
      (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
        (PrimeSpectrum.basicOpen (a * b * (a + b))))^*[AddCommGrpCat.{u + 1}]).obj F) n))
    (x : Sheaf.H
      (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
        (PrimeSpectrum.basicOpen (a + b)))^*[AddCommGrpCat.{u + 1}]).obj F) (n + 1))
    (ha : cohomologyMap
      (Scheme.homOfLE (X := Spec (CommRingCat.of R))
        (PrimeSpectrum.basicOpen_mul_le_right a (a + b)))
      (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
        (PrimeSpectrum.basicOpen (a + b)))^*[AddCommGrpCat.{u + 1}]).obj F) (n + 1) x = 0)
    (hb : cohomologyMap
      (Scheme.homOfLE (X := Spec (CommRingCat.of R))
        (PrimeSpectrum.basicOpen_mul_le_right b (a + b)))
      (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
        (PrimeSpectrum.basicOpen (a + b)))^*[AddCommGrpCat.{u + 1}]).obj F) (n + 1) x = 0) :
    x = 0 := by
  let X := Spec (CommRingCat.of R)
  let W : X.Opens := PrimeSpectrum.basicOpen (a + b)
  let U : W.toScheme.Opens := W.ι ⁻¹ᵁ PrimeSpectrum.basicOpen a
  let V : W.toScheme.Opens := W.ι ⁻¹ᵁ PrimeSpectrum.basicOpen b
  let G := ((W.ι)^*[AddCommGrpCat.{u + 1}]).obj F
  have hcover : U ⊔ V = ⊤ := by
    ext z
    change (a ∉ z.val.asIdeal ∨ b ∉ z.val.asIdeal) ↔ True
    constructor
    · intro _; trivial
    · intro _
      have hz : a + b ∉ z.val.asIdeal := z.property
      by_cases ha' : a ∈ z.val.asIdeal
      · exact Or.inr (fun hb' ↦ hz (z.val.asIdeal.add_mem ha' hb'))
      · exact Or.inl ha'
  have hUeq : W.ι ''ᵁ U = PrimeSpectrum.basicOpen (a * (a + b)) := by
    dsimp [U]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    dsimp [W]
    rw [PrimeSpectrum.basicOpen_mul]
    exact inf_comm _ _
  have hVeq : W.ι ''ᵁ V = PrimeSpectrum.basicOpen (b * (a + b)) := by
    dsimp [V]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    dsimp [W]
    rw [PrimeSpectrum.basicOpen_mul]
    exact inf_comm _ _
  let eU := W.ι.isoImage U ≪≫ X.isoOfEq hUeq
  let eV := W.ι.isoImage V ≪≫ X.isoOfEq hVeq
  have hUc : U.ι = eU.hom ≫
      X.homOfLE (PrimeSpectrum.basicOpen_mul_le_right a (a + b)) := by
    apply (cancel_mono W.ι).1
    change U.ι ≫ W.ι = (W.ι.isoImage U).hom ≫
      (X.isoOfEq hUeq).hom ≫
        (X.homOfLE (PrimeSpectrum.basicOpen_mul_le_right a (a + b)) ≫ W.ι)
    rw [X.homOfLE_ι (PrimeSpectrum.basicOpen_mul_le_right a (a + b))]
    rw [X.isoOfEq_hom_ι hUeq]
    exact (W.ι.isoImage_hom_ι U).symm
  have hVc : V.ι = eV.hom ≫
      X.homOfLE (PrimeSpectrum.basicOpen_mul_le_right b (a + b)) := by
    apply (cancel_mono W.ι).1
    change V.ι ≫ W.ι = (W.ι.isoImage V).hom ≫
      (X.isoOfEq hVeq).hom ≫
        (X.homOfLE (PrimeSpectrum.basicOpen_mul_le_right b (a + b)) ≫ W.ι)
    rw [X.homOfLE_ι (PrimeSpectrum.basicOpen_mul_le_right b (a + b))]
    rw [X.isoOfEq_hom_ι hVeq]
    exact (W.ι.isoImage_hom_ι V).symm
  have hU : cohomologyMap U.ι G (n + 1) x = 0 := by
    rw [hUc]
    let j := X.homOfLE (PrimeSpectrum.basicOpen_mul_le_right a (a + b))
    let e := (upperStarComp AddCommGrpCat.{u + 1} eU.hom j).app G
    have he := (cohomologyPullbackFunctorial eU.hom j G (n + 1)).2.1 x
    rw [ha, map_zero] at he
    have he' := congrArg (Sheaf.H.map e.inv (n + 1)) he
    simpa [e, ← Sheaf.H.map_comp_apply] using he'.symm
  have hV : cohomologyMap V.ι G (n + 1) x = 0 := by
    rw [hVc]
    let j := X.homOfLE (PrimeSpectrum.basicOpen_mul_le_right b (a + b))
    let e := (upperStarComp AddCommGrpCat.{u + 1} eV.hom j).app G
    have he := (cohomologyPullbackFunctorial eV.hom j G (n + 1)).2.1 x
    rw [hb, map_zero] at he
    have he' := congrArg (Sheaf.H.map e.inv (n + 1)) he
    simpa [e, ← Sheaf.H.map_comp_apply] using he'.symm
  have hIeq : W.ι ''ᵁ (U ⊓ V) = PrimeSpectrum.basicOpen (a * b * (a + b)) := by
    dsimp [U, V]
    rw [← Scheme.Hom.preimage_inf, ← PrimeSpectrum.basicOpen_mul,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    dsimp [W]
    simp only [PrimeSpectrum.basicOpen_mul]
    ac_rfl
  let I : W.toScheme.Opens := U ⊓ V
  let B : X.Opens := PrimeSpectrum.basicOpen (a * b * (a + b))
  let eI : I.toScheme ≅ B.toScheme := W.ι.isoImage I ≪≫ X.isoOfEq hIeq
  let Q := ((B.ι)^*[AddCommGrpCat.{u + 1}]).obj F
  have hIc : I.ι ≫ W.ι = eI.hom ≫ B.ι := by
    change I.ι ≫ W.ι = (W.ι.isoImage I).hom ≫ (X.isoOfEq hIeq).hom ≫ B.ι
    rw [X.isoOfEq_hom_ι hIeq]
    exact (W.ι.isoImage_hom_ι I).symm
  let eCoeff : ((eI.hom)^*[AddCommGrpCat.{u + 1}]).obj Q ≅
      ((I.ι)^*[AddCommGrpCat.{u + 1}]).obj G :=
    ((upperStarComp AddCommGrpCat.{u + 1} eI.hom B.ι (I.ι ≫ W.ι) hIc).app F).symm ≪≫
      (upperStarComp AddCommGrpCat.{u + 1} I.ι W.ι).app F
  have hs : Subsingleton (Sheaf.H (((eI.hom)^*[AddCommGrpCat.{u + 1}]).obj Q) n) :=
    (Equiv.subsingleton_congr
      (Equiv.ofBijective (cohomologyMap eI.hom Q n)
        (cohomologyMap_bijective eI.hom Q n))).mp hprev
  have hI : Subsingleton
      (Sheaf.H (((U ⊓ V).ι)^*[AddCommGrpCat.{u + 1}].obj G) n) := by
    let ee := (Sheaf.functorH I.toScheme.smallEtaleTopology n).mapIso eCoeff
    exact (Equiv.subsingleton_congr ee.addCommGroupIsoToAddEquiv.toEquiv).mp hs
  exact cohomologyMap_joint_zero U V hcover G n hI x hU hV

end AlgebraicGeometry.Etale
