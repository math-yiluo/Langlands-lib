import Langlands.GroupScheme.GeneratedFamily
import Langlands.GroupScheme.Cartan.Induction
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.Torus.CentralizerConnected
import Langlands.GroupScheme.Torus.FiniteHomMaximalitySmooth
import Langlands.GroupScheme.Torus.FiniteHomCentralizer
import Langlands.AbelianScheme.Isogeny

/-! # Reflection of Cartan generation through finite surjections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- Cartan generation reflects through a finite surjection when every maximal
target torus lifts to a closed torus surjecting onto it. -/
def FiniteHomCartanGenerationReflectionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (q : G ⟶ H) [IsFinite q.hom.hom.left] [Surjective q.hom.hom.left],
    (∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ H),
      IsMaximalTorus s →
        ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
          (f : T.toGrp ⟶ S.toGrp),
          IsTorus T.toGrp ∧ IsClosedSubgroup t ∧
            Surjective f.hom.hom.left ∧ t ≫ q = f ≫ s) →
    IsGeneratedByCartanSubgroups H → IsGeneratedByCartanSubgroups G

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Smooth generated envelopes, centralizer transport and integral finite-map
rigidity reflect generation without regularity assumptions on closed competitors. -/
theorem isGeneratedByCartanSubgroups_of_finiteHom
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (q : G ⟶ H) [IsFinite q.hom.hom.left] [Surjective q.hom.hom.left]
    (hlift : ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ H),
      IsMaximalTorus s →
        ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
          (f : T.toGrp ⟶ S.toGrp),
          IsTorus T.toGrp ∧ IsClosedSubgroup t ∧
            Surjective f.hom.hom.left ∧ t ≫ q = f ≫ s)
    (hH : IsGeneratedByCartanSubgroups H) : IsGeneratedByCartanSubgroups G := by
  classical
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let J := Σ C : GroupScheme (Spec (CommRingCat.of k)), {c : C ⟶ G // IsCartanSubgroup c}
  let A : J → GroupScheme (Spec (CommRingCat.of k)) := fun j => j.1
  let a : ∀ j, A j ⟶ G := fun j => j.2.val
  have hA : ∀ j, Smooth (A j).X.hom ∧ IsAffineHom (A j).X.hom ∧
      ConnectedSpace (A j).X.left := by
    intro j
    have hc := j.2.property
    have hsc := hc.smooth_connected
    exact ⟨hsc.1, hc.1.isAffineHom, hsc.2⟩
  obtain ⟨D, d, hsmD, haffD, hconnD, hd⟩ :=
    FiniteGeneration.exists_smooth_generated_family (A := A) (a := a) hA
  let : Smooth D.X.hom := hsmD
  let : IsAffineHom D.X.hom := haffD
  let : ConnectedSpace D.X.left := hconnD
  obtain ⟨E, e, p, heclosed, he, hpflat, hpsurj, hpqc, hpfp, hsmE, hconnE, haffE⟩ :=
    HomImage.exists_image (d ≫ q)
  let : Smooth E.X.hom := hsmE
  let : IsAffineHom E.X.hom := haffE
  let : ConnectedSpace E.X.left := hconnE
  have hE : SubgroupFunctor.range e = ⊤ := by
    apply hH E e heclosed
    intro C' c' hc'
    obtain ⟨S, s, hs, hrep'⟩ := hc'.exists_centralizer_representation
    obtain ⟨T, t, f, hT, ht, hfsurj, hcomm⟩ := hlift S s hs
    let : Surjective f.hom.hom.left := hfsurj
    have htmax : IsMaximalTorus t := hs.of_finiteHom q t s f hT ht hcomm
    obtain ⟨C, c, hc, hrep⟩ := exists_isCartanSubgroup_of_isMaximalTorus htmax
    have hcd : FactorsThrough c.hom.hom d := hd.2.1 ⟨C, ⟨c, hc⟩⟩
    have hcle : SubgroupFunctor.range (c ≫ q) ≤ SubgroupFunctor.range e := by
      obtain ⟨v, hv⟩ := hcd
      intro U x hx
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      apply SubgroupFunctor.mem_range.mpr
      refine ⟨y ≫ v ≫ p.hom.hom, ?_⟩
      have hpe := congrArg (fun r => r.hom.hom) he
      simp only [Grp.comp_hom_hom] at hpe
      simp only [Grp.comp_hom_hom, Category.assoc]
      rw [hpe, ← Category.assoc v d.hom.hom q.hom.hom, hv]
    let : Smooth C'.X.hom :=
      torusCentralizerSmooth k H S s hs.1 hs.2.1 C' c' hrep' hc'.1
    apply (factorsThrough_hom_iff_range_le c' e).2
    exact range_torusCentralizer_le_of_finiteSurjective
      q hT t s f hcomm c hrep c' hrep' e heclosed hcle
  have hid : (𝟙 H.X) ∈ (SubgroupFunctor.range e).carrier H.X := by
    rw [hE]
    exact Subgroup.mem_top _
  obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hid
  have hvleft : v.left ≫ e.hom.hom.left = 𝟙 H.X.left :=
    congrArg (fun r => r.left) hv
  let : Surjective (v.left ≫ e.hom.hom.left) := by
    rw [hvleft]
    infer_instance
  let : Surjective e.hom.hom.left := Surjective.of_comp v.left e.hom.hom.left
  let : Surjective p.hom.hom.left := hpsurj
  let : Surjective (d.hom.hom.left ≫ q.hom.hom.left) := by
    change Surjective (d ≫ q).hom.hom.left
    rw [← he]
    change Surjective (p.hom.hom.left ≫ e.hom.hom.left)
    infer_instance
  let : IsReduced H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k H.X.left H.X.hom
  let : IsSchemeTheoreticallyDominant (d.hom.hom.left ≫ q.hom.hom.left) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  let : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : GeometricallyIntegral G.X.hom :=
    smoothConnectedAffineGeometry.1 k G inferInstance inferInstance inferInstance
  let : IsIntegral G.X.left := GeometricallyIntegral.isIntegral_of_subsingleton G.X.hom
  let : Nonempty H.X.left := ⟨q.hom.hom.left (Classical.choice inferInstance)⟩
  let : IsClosedImmersion d.hom.hom.left := hd.1
  let : IsIso d.hom.hom.left :=
    isIso_of_closedImmersion_finite_comp_schematic d.hom.hom.left q.hom.hom.left
  let : IsIso d.hom.hom :=
    (isIso_iff_of_reflects_iso _ (Over.forget _)).mp
      (show IsIso d.hom.hom.left from inferInstance)
  intro K i hi hcartan
  have hle : SubgroupFunctor.range d ≤ SubgroupFunctor.range i :=
    hd.2.2 K i hi (fun j => hcartan j.1 j.2.val j.2.property)
  apply SubgroupFunctor.ext
  intro U
  apply top_unique
  intro x _
  apply hle U
  exact SubgroupFunctor.mem_range.mpr ⟨x ≫ inv d.hom.hom, by simp⟩

/-- The finite-map reflection statement holds over every field and universe. -/
theorem finiteHomCartanGenerationReflectionStatement :
    FiniteHomCartanGenerationReflectionStatement.{u} := by
  intro k _ G H _ _ _ _ _ q _ _ hlift hH
  exact isGeneratedByCartanSubgroups_of_finiteHom q hlift hH

/-- The torus-lifting premise delivered by the semisimple isogeny reduction
implies the finite-map premise used for generation reflection. -/
theorem isGeneratedByCartanSubgroups_of_isogeny
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (q : G ⟶ H) (hq : IsIsogeny q)
    (hlift : ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ H),
      IsTorus S.toGrp → IsClosedSubgroup s →
        ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
          (f : T.toGrp ⟶ S.toGrp),
          IsTorus T.toGrp ∧ IsClosedSubgroup t ∧ IsIsogeny f ∧ t ≫ q = f ≫ s)
    (hH : IsGeneratedByCartanSubgroups H) : IsGeneratedByCartanSubgroups G := by
  let : IsFinite q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.2
  apply isGeneratedByCartanSubgroups_of_finiteHom q _ hH
  intro S s hs
  obtain ⟨T, t, f, hT, ht, hf, hcomm⟩ := hlift S s hs.1 hs.2.1
  exact ⟨T, t, f, hT, ht, hf.2.2, hcomm⟩

end Langlands.GroupScheme
