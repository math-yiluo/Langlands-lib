import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeCentralizerSmooth
import Langlands.GroupScheme.Torus.AffineCentralizerQuotient
import Langlands.GroupScheme.HomogeneousQuotientFiniteCover
import Langlands.GroupScheme.HomogeneousQuotientLocalModels
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact

/-! # Smooth quasi-affine quotients by multiplicative-type centralizers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
open Langlands.GroupScheme.RelativeMultiplicativeType

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- Every representative of the centralizer of a closed diagonalizable
subgroup over a spectrum admits a quasi-affine actual quotient. -/
theorem diagonalizableCentralizer_exists_quasiAffine_quotient_overSpec
    {R : CommRingCat.{u}} {G Z : GroupScheme (Spec R)} {H : CommGroupScheme (Spec R)}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H.toGrp ⟶ G) (hH : IsDiagonalizable H.toGrp) (hi : IsClosedSubgroup i)
    (z : Z ⟶ G) (hz : (torusCentralizer i).IsRepresentedBy z) :
    ∃ Q : HomogeneousQuotient z, Q.scheme.left.IsQuasiAffine := by
  obtain ⟨M, _, _, ⟨e⟩⟩ := hH
  let e' : H.toGrp ≅ (Diagonalizable.groupScheme R M).toGrp :=
    e ≪≫ Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec R)) M
  have hi' : IsClosedSubgroup (e'.inv ≫ i) := (IsClosedSubgroup.of_iso e'.symm).comp hi
  have hz' : (torusCentralizer (e'.inv ≫ i)).IsRepresentedBy z := by
    rw [torusCentralizer_eq_centralizer_range]
    change (SubgroupFunctor.range (e'.symm.hom ≫ i)).centralizer.IsRepresentedBy z
    rw [SubgroupFunctor.range_iso_comp e'.symm i, ← torusCentralizer_eq_centralizer_range]
    exact hz
  obtain ⟨Q, _, hQ⟩ :=
    diagonalizableCentralizer_exists_quasiAffine_quotient_overRing (e'.inv ≫ i) hi' z hz'
  have htop : (⊤ : Q.scheme.left.Opens).toScheme.IsQuasiAffine := by
    simpa using hQ ⟨⊤, isAffineOpen_top (Spec R)⟩
  let : (⊤ : Q.scheme.left.Opens).toScheme.IsQuasiAffine := htop
  exact ⟨Q, Scheme.IsQuasiAffine.of_isAffineHom Q.scheme.left.topIso.inv⟩

/-- Over any affine base, centralizers of closed multiplicative-type subgroups
have actual quasi-affine homogeneous quotients. -/
theorem relativeMultiplicativeTypeCentralizer_exists_quasiAffine_quotient_affine
    {S : Scheme.{u}} [IsAffine S] {G Z : GroupScheme S} {H : CommGroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H.toGrp ⟶ G) (hH : IsMultiplicativeType H.toGrp) (hi : IsClosedSubgroup i)
    (z : Z ⟶ G) (hz : (torusCentralizer i).IsRepresentedBy z) :
    ∃ Q : HomogeneousQuotient z, Q.scheme.left.IsQuasiAffine := by
  classical
  let : Mono z.hom.hom := hz.1
  have hZ : Smooth Z.X.hom := relativeMultiplicativeTypeCentralizer_smooth i hH z hz
  obtain ⟨𝒰, h𝒰⟩ := hH
  have hprop (k : 𝒰.I₀) : Flat (𝒰.f k) ∧ LocallyOfFinitePresentation (𝒰.f k) :=
    𝒰.map_prop k
  have : QuasiCompactCover 𝒰.toPreZeroHypercover := .of_isOpenMap fun k => by
    have := (hprop k).1
    have := (hprop k).2
    exact (𝒰.f k).isOpenMap
  obtain ⟨𝒱, f, hfin, _⟩ := QuasiCompactCover.exists_hom 𝒰
  let : Finite 𝒱.I₀ := hfin
  have (k : 𝒱.I₀) : Flat (𝒱.f k) := (𝒱.map_prop k).1
  have (k : 𝒱.I₀) : LocallyOfFinitePresentation (𝒱.f k) := (𝒱.map_prop k).2
  have hsplit (k : 𝒱.I₀) : IsDiagonalizable
      ((GroupScheme.baseChange (𝒱.f k)).obj H.toGrp) :=
    IsDiagonalizable.of_iso
      (Descent.pullbackComparison (𝒰.f (f.s₀ k)) (f.h₀ k) (𝒱.f k) (f.w₀ k) H.toGrp).symm
      ((h𝒰 (f.s₀ k)).baseChange (f.h₀ k))
  let Q := HomogeneousQuotientSheaf.quotientOfFiniteAffineCover z hZ
    (fun k => Spec (𝒱.X k)) 𝒱.f (fun s => 𝒱.cover.exists_eq s) (fun k => by
      let b := 𝒱.f k
      let B := GroupScheme.baseChange b
      let : Smooth (B.obj G).X.hom := MorphismProperty.pullback_snd G.X.hom b inferInstance
      let : IsAffineHom (B.obj G).X.hom :=
        MorphismProperty.pullback_snd G.X.hom b inferInstance
      have hz' := hz.baseChange b
      rw [← torusCentralizer_baseChange] at hz'
      exact diagonalizableCentralizer_exists_quasiAffine_quotient_overSpec
        (H := (CommGroupScheme.baseChange b).obj H) (B.map i) (hsplit k)
        (hi.baseChange b) (B.map z) hz')
  exact ⟨Q.val, Q.property.2⟩

/-- Over an arbitrary scheme, every supplied representative of a
multiplicative-type centralizer has a smooth quotient quasi-affine over the base. -/
theorem relativeMultiplicativeTypeCentralizer_exists_quasiAffine_quotient
    {S : Scheme.{u}} {G Z : GroupScheme S} {H : CommGroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H.toGrp ⟶ G) (hH : IsMultiplicativeType H.toGrp) (hi : IsClosedSubgroup i)
    (z : Z ⟶ G) (hz : (torusCentralizer i).IsRepresentedBy z) :
    ∃ Q : HomogeneousQuotient z, Smooth Q.scheme.hom ∧
      ∀ U : S.affineOpens, (Q.scheme.hom ⁻¹ᵁ (U : S.Opens)).toScheme.IsQuasiAffine := by
  let : Mono z.hom.hom := hz.1
  have hZ : Smooth Z.X.hom := relativeMultiplicativeTypeCentralizer_smooth i hH z hz
  apply HomogeneousQuotientSheaf.exists_quotient_of_affine_local_models z hZ
  intro T b _ _
  let B := GroupScheme.baseChange b
  let : Smooth (B.obj G).X.hom := MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffineHom (B.obj G).X.hom := MorphismProperty.pullback_snd G.X.hom b inferInstance
  have hz' := hz.baseChange b
  rw [← torusCentralizer_baseChange] at hz'
  exact relativeMultiplicativeTypeCentralizer_exists_quasiAffine_quotient_affine
    (H := (CommGroupScheme.baseChange b).obj H) (B.map i) (hH.baseChange b)
    (hi.baseChange b) (B.map z) hz'

/-- Choose the smooth relatively quasi-affine multiplicative-type centralizer quotient. -/
def relativeMultiplicativeTypeCentralizerQuotient
    {S : Scheme.{u}} {G Z : GroupScheme S} {H : CommGroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H.toGrp ⟶ G) (hH : IsMultiplicativeType H.toGrp) (hi : IsClosedSubgroup i)
    (z : Z ⟶ G) (hz : (torusCentralizer i).IsRepresentedBy z) :
    {Q : HomogeneousQuotient z // Smooth Q.scheme.hom ∧
      ∀ U : S.affineOpens, (Q.scheme.hom ⁻¹ᵁ (U : S.Opens)).toScheme.IsQuasiAffine} :=
  ⟨_, (relativeMultiplicativeTypeCentralizer_exists_quasiAffine_quotient i hH hi z hz).choose_spec⟩

end Langlands.GroupScheme
