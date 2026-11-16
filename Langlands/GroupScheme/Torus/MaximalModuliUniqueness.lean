import Langlands.GroupScheme.Torus.MaximalModuliRestriction
import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport
import Langlands.GroupScheme.HomScheme.AdmissiblePresheaf
import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Uniqueness of supplied universal maximal-torus families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {M N T : Over S}
  {K : CommGroupScheme M.left} {L : CommGroupScheme N.left}

/-- Evaluation of a fibrewise maximal family remains fibrewise maximal in a
smooth affine ambient group. -/
theorem isFibrewiseMaximalTorus_familyHom
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (j : K.toGrp ⟶ (baseChange M.hom).obj G)
    (hm : IsFibrewiseMaximalTorus j) (a : T ⟶ M) :
    IsFibrewiseMaximalTorus
      (T := (CommGroupScheme.baseChange a.left).obj K) (familyHom j a) := by
  let : Smooth ((baseChange M.hom).obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom M.hom))
  let : IsAffineHom ((baseChange M.hom).obj G).X.hom :=
    MorphismProperty.pullback_snd _ _ ‹IsAffineHom G.X.hom›
  exact (hm.baseChange a.left).comp_iso
    (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) G)

/-- The all-test universal property makes family evaluation injective. -/
theorem IsUniversalMaximal.evaluate_injective
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {j : K.toGrp ⟶ (baseChange M.hom).obj G}
    (huni : IsUniversalMaximal j) (hK : RelativeTorus.IsTorus K.toGrp)
    (hj : IsClosedSubgroup j) (hm : IsFibrewiseMaximalTorus j) :
    Function.Injective (evaluate j (T := T)) := by
  intro a b hab
  obtain ⟨c, hc, huc⟩ := huni T ((CommGroupScheme.baseChange b.left).obj K)
    (familyHom j b) (hK.baseChange b.left)
    (isClosedSubgroup_familyHom j hj b)
    (isFibrewiseMaximalTorus_familyHom j hm b)
  exact (huc a hab).trans (huc b rfl).symm

/-- Two supplied universal maximal-torus families have uniquely isomorphic
parameter schemes over the original base. -/
def universalMaximalIso
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (j : K.toGrp ⟶ (baseChange M.hom).obj G)
    (i : L.toGrp ⟶ (baseChange N.hom).obj G)
    (hK : RelativeTorus.IsTorus K.toGrp) (hj : IsClosedSubgroup j)
    (hm : IsFibrewiseMaximalTorus j) (huni : IsUniversalMaximal j)
    (hL : RelativeTorus.IsTorus L.toGrp) (hi : IsClosedSubgroup i)
    (hn : IsFibrewiseMaximalTorus i) (huni' : IsUniversalMaximal i) : N ≅ M := by
  apply Classical.choice
  obtain ⟨a, ha, hua⟩ := huni N L i hL hi hn
  obtain ⟨b, hb, hub⟩ := huni' M K j hK hj hm
  refine ⟨⟨a, b, ?_, ?_⟩⟩
  · apply huni'.evaluate_injective hL hi hn
    rw [← evaluate_comp, evaluate_eq_of_range_eq _ _ hb a, ha, evaluate_id]
  · apply huni.evaluate_injective hK hj hm
    rw [← evaluate_comp, evaluate_eq_of_range_eq _ _ ha b, hb, evaluate_id]

/-- Quasi-affineness above every affine open of the base transports through
an isomorphism over that base. -/
theorem quasiAffineOver_of_iso (e : M ≅ N)
    (hN : ∀ V : S.affineOpens, (N.hom ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine) :
    ∀ V : S.affineOpens, (M.hom ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine := by
  intro V
  let : (N.hom ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine := hN V
  let f := e.hom.left
  have : IsIso f := inferInstance
  have h := Scheme.IsQuasiAffine.of_isAffineHom
    (f.preimageIso (N.hom ⁻¹ᵁ (V : S.Opens))).hom
  dsimp only [f] at h
  simpa only [← Scheme.Hom.comp_preimage, Over.w e.hom] using h

end Langlands.GroupScheme.TorusSubgroupModuli
