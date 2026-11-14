import Langlands.GroupScheme.RelativeLevi.BorelLocus
import Langlands.GroupScheme.RelativeLevi.BorelLocusStatement
import Langlands.GroupScheme.RelativeLevi.SplitMaximalTorusChartStatement
import Langlands.GroupScheme.RelativeLevi.BorelWeightRankLocus
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Geometric-fibre and étale-local reductions for the Borel locus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- Internal reduction from affine étale split maximal-torus charts to
clopenness of the Borel locus. -/
def RelativeBorelLocusClopenReductionStatement : Prop :=
  RelativeParabolicSplitMaximalTorusChartStatement.{u} →
    RelativeBorelLocusClopenStatement.{u}

end Langlands.GroupScheme

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {G P : GroupScheme S} {i : P ⟶ G}

/-- The residue-field geometric Borel condition is the Borel condition on the
actual chosen geometric fibre. -/
theorem isGeometricBorelSubgroup_residueFiber_iff
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i) (s : S) :
    IsGeometricBorelSubgroup (residueFiberHom i s) ↔
      IsBorelSubgroup (geometricFiberHom i s) := by
  let a := S.fromSpecResidueField s
  let b := toAlgebraicClosure (S.residueField s)
  let eP := Descent.pullbackComparison a b (geometricPoint S s) rfl P
  let eG := Descent.pullbackComparison a b (geometricPoint S s) rfl G
  constructor
  · intro hb
    have h := (hb.2.iso_comp eP.symm).comp_iso eG
    change IsBorelSubgroup
      ((eP.inv ≫ (baseChange b).map ((baseChange a).map i)) ≫ eG.hom) at h
    rw [Category.assoc, Descent.pullbackComparison_naturality,
      Iso.inv_hom_id_assoc] at h
    exact h
  · intro hb
    let : IsAffineHom ((baseChange a).obj G).X.hom :=
      (hG.isConnectedReductive_residueFiber s).isAffineHom
    apply isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure
      (hclosed := (hi.residueFiber s).isClosedSubgroup)
    have h := (hb.iso_comp eP).comp_iso eG.symm
    change IsBorelSubgroup
      ((eP.hom ≫ (baseChange (geometricPoint S s)).map i) ≫ eG.inv) at h
    rw [← Descent.pullbackComparison_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] at h
    exact h

/-- Openness can be tested on a pointwise family of étale charts. -/
theorem isOpen_of_etale_local_preimage (A : Set S)
    (h : ∀ s : S, ∃ (U : Scheme.{u}) (f : U ⟶ S), Etale f ∧
      ∃ t : U, f t = s ∧ IsOpen (f ⁻¹' A)) : IsOpen A := by
  refine isOpen_iff_forall_mem_open.mpr fun s hs => ?_
  obtain ⟨U, f, hf, t, ht, hA⟩ := h s
  let : Etale f := hf
  refine ⟨f '' (f ⁻¹' A), ?_, f.isOpenMap _ hA, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hx
  · exact ⟨t, show f t ∈ A from ht.symm ▸ hs, ht⟩

/-- Clopenness can be tested on a pointwise family of étale charts. -/
theorem isClopen_of_etale_local_preimage (A : Set S)
    (h : ∀ s : S, ∃ (U : Scheme.{u}) (f : U ⟶ S), Etale f ∧
      ∃ t : U, f t = s ∧ IsClopen (f ⁻¹' A)) : IsClopen A := by
  refine ⟨?_, isOpen_of_etale_local_preimage A ?_⟩
  · apply isOpen_compl_iff.mp
    apply isOpen_of_etale_local_preimage Aᶜ
    intro s
    obtain ⟨U, f, hf, t, ht, hA⟩ := h s
    exact ⟨U, f, hf, t, ht, hA.compl.isOpen⟩
  · intro s
    obtain ⟨U, f, hf, t, ht, hA⟩ := h s
    exact ⟨U, f, hf, t, ht, hA.isOpen⟩

/-- The Borel locus is clopen if the Borel loci on a pointwise family of
étale charts are clopen. -/
theorem isClopen_borelLocus_of_etale_charts
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (h : ∀ s : S, ∃ (U : Scheme.{u}) (f : U ⟶ S), Etale f ∧
      ∃ t : U, f t = s ∧ IsClopen (borelLocus ((baseChange f).map i))) :
    IsClopen (borelLocus i) := by
  apply isClopen_of_etale_local_preimage
  intro s
  obtain ⟨U, f, hf, t, ht, hB⟩ := h s
  rw [borelLocus_baseChange i hG hi f] at hB
  exact ⟨U, f, hf, t, ht, hB⟩

/-- On an affine chart containing a split torus that is geometrically maximal
in the ambient group, the Borel locus is the no-opposite-weight rank locus. -/
theorem borelLocus_eq_noOppositeWeightRankLocus
    {r : Type u} [CommRing r]
    {G P : GroupScheme (Spec (CommRingCat.of r))}
    (i : P ⟶ G) (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (I : Type u) [Fintype I] [DecidableEq I]
    (j : splitTorus (Spec (CommRingCat.of r)) I ⟶ P)
    (hmax : ∀ x : Spec (CommRingCat.of r),
      IsMaximalTorus (T := splitTorus.commGroupScheme
        (Spec (CommRingCat.of
          (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField x)))) I)
        ((splitTorus.baseChangeIso (geometricPoint _ x) I).inv ≫
          (baseChange (geometricPoint _ x)).map (j ≫ i))) :
    let _ : IsAffineHom P.X.hom := hi.isAffineHom
    let _ : Smooth P.X.hom := hi.smooth
    borelLocus i = splitTorus.noOppositeWeightRankLocus I P j := by
  let : IsAffineHom P.X.hom := hi.isAffineHom
  let : Smooth P.X.hom := hi.smooth
  ext s
  change IsGeometricBorelSubgroup (residueFiberHom i s) ↔ _
  rw [isGeometricBorelSubgroup_residueFiber_iff hG hi s]
  have hGbar := hG.isConnectedReductive_baseChange (geometricPoint _ s)
  let : IsAffineHom (geometricFiber G s).X.hom := hGbar.isAffineHom
  let : IsAffineHom (geometricFiber P s).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd P.X.hom (geometricPoint _ s)))
  apply splitTorus.isBorelSubgroup_iff_no_opposite_exponent_weight_finranks
    I hGbar (geometricFiberHom i s) (splitTorus.geometricFiberHom I P j s)
    ?_ (hi.isParabolicSubgroup_baseChange hG (geometricPoint _ s))
  simpa only [splitTorus.geometricFiberHom, geometricFiberHom,
    Functor.map_comp, Category.assoc] using hmax s

/-- The Borel locus is clopen on an affine chart with a geometrically maximal
standard split torus in the parabolic. -/
theorem isClopen_borelLocus_of_splitMaximalTorus
    {r : Type u} [CommRing r]
    {G P : GroupScheme (Spec (CommRingCat.of r))}
    (i : P ⟶ G) (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (I : Type u) [Fintype I] [DecidableEq I]
    (j : splitTorus (Spec (CommRingCat.of r)) I ⟶ P)
    (hmax : ∀ x : Spec (CommRingCat.of r),
      IsMaximalTorus (T := splitTorus.commGroupScheme
        (Spec (CommRingCat.of
          (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField x)))) I)
        ((splitTorus.baseChangeIso (geometricPoint _ x) I).inv ≫
          (baseChange (geometricPoint _ x)).map (j ≫ i))) :
    IsClopen (borelLocus i) := by
  let : IsAffineHom P.X.hom := hi.isAffineHom
  let : Smooth P.X.hom := hi.smooth
  rw [borelLocus_eq_noOppositeWeightRankLocus i hG hi I j hmax]
  exact splitTorus.isClopen_noOppositeWeightRankLocus I P j

end Langlands.GroupScheme.RelativeLevi

namespace Langlands.GroupScheme

/-- Affine étale split maximal-torus charts imply clopenness of the Borel
locus on every base scheme. -/
theorem relativeBorelLocusClopen_of_splitMaximalTorusCharts
    : RelativeBorelLocusClopenReductionStatement.{u} := by
  intro hcharts S G P i hG hi
  apply RelativeLevi.isClopen_borelLocus_of_etale_charts hG hi
  intro s
  obtain ⟨r, hr, f, hf, t, ht, I, hI, hIeq, j, _, hmax⟩ :=
    hcharts S G P i hG hi s
  let : CommRing r := hr
  let : Fintype I := hI
  let : DecidableEq I := hIeq
  exact ⟨_, f, hf, t, ht,
    RelativeLevi.isClopen_borelLocus_of_splitMaximalTorus
      ((baseChange f).map i) (hG.baseChange f) (hi.baseChange hG f) I j hmax⟩

end Langlands.GroupScheme
