import Langlands.GroupScheme.HomScheme.TorusCentralizerChartGluing
import Langlands.GroupScheme.HomScheme.TorusCentralizerJetChart
import Langlands.GroupScheme.HomScheme.TorusCentralizerJetCoverage

/-! # Representability of fibrewise torus centralizers by finite-jet charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

open IdentityJet SubgroupFunctor

private theorem centralizerResidueFibres_evaluate {S : Scheme.{u}} {G : GroupScheme S}
    (hG : HasAffineResidueFibers G) {T A : Over S} {H : GroupScheme T.left}
    (i : H ⟶ (baseChange T.hom).obj G) [Smooth H.X.hom]
    (hi : IsClosedSubgroup i) (hf : HasTorusCentralizerResidueFibres i) (a : A ⟶ T) :
    HasTorusCentralizerResidueFibres (familyHom i a) := by
  apply (hasTorusCentralizerResidueFibres_familyHom_iff i a).mpr
  exact (range_subset_torusCentralizerResidueLocus_iff (hG.baseChange T.hom) i hi a.left).mp
    (fun _ _ => hf _)

/-- A separated smooth quasi-compact group with geometrically connected affine
residue fibres over a noetherian affine base has the actual locally finite-type
parameter of smooth geometrically connected fibrewise torus centralizers. -/
def NoetherianAffineFibrewiseTorusCentralizersRepresentableStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (G : GroupScheme (Spec R))
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    [GeometricallyConnected G.X.hom], HasAffineResidueFibers G → FibrewiseTorusCentralizersRepresentable G

set_option maxHeartbeats 1400000 in
theorem noetherianAffineFibrewiseTorusCentralizersRepresentable :
    NoetherianAffineFibrewiseTorusCentralizersRepresentableStatement.{u} := by
  intro R _ G _ _ _ _ hG
  classical
  let I := ULift.{u} (ℕ × ℕ)
  choose U H j hfinite hclosed hsmooth hconn hfibres hclass using
    fun k : I => torusCentralizerJetChart R G hG k.down.1 k.down.2
  have hopens (k : I) : IsOpenCentralizerChart (j k) := by
    refine ⟨hfinite k, hclosed k, hsmooth k, hconn k, hfibres k, ?_, ?_⟩
    · intro T a b he
      have : Smooth ((baseChange a.left).obj (H k)).X.hom := by
        have := hsmooth k
        exact inferInstanceAs (Smooth (pullback.snd (H k).X.hom a.left))
      have : GeometricallyConnected ((baseChange a.left).obj (H k)).X.hom := by
        have := hconn k
        exact inferInstanceAs (GeometricallyConnected (pullback.snd (H k).X.hom a.left))
      have hc := hclass k T ((baseChange a.left).obj (H k)) (familyHom (j k) a)
        (isClosedSubgroup_familyHom (j k) (hclosed k) a)
      exact hc.1 a b rfl he.symm
    · intro T L i hi hLs hLg hLf
      have : Smooth L.X.hom := hLs
      have : GeometricallyConnected L.X.hom := hLg
      have : IsSeparated ((baseChange T.hom).obj G).X.hom :=
        inferInstanceAs (IsSeparated (pullback.snd G.X.hom T.hom))
      have : IsClosedImmersion i.hom.hom.left := hi
      have : IsSeparated L.X.hom := by rw [← Over.w i.hom.hom]; infer_instance
      obtain ⟨V, hV⟩ := exists_smoothGroupFixedRankOpen L k.down.2
      obtain ⟨D, hD⟩ := identityJetStabilizerParameter R G k.down.1
      obtain ⟨W, hW⟩ := exists_open_of_openInStabilizer_familyHom k.down.1 D hD i hi
      refine ⟨V ⊓ W, fun A a => ?_⟩
      have : Smooth ((baseChange a.left).obj L).X.hom :=
        inferInstanceAs (Smooth (pullback.snd L.X.hom a.left))
      have : GeometricallyConnected ((baseChange a.left).obj L).X.hom :=
        inferInstanceAs (GeometricallyConnected (pullback.snd L.X.hom a.left))
      have hf := centralizerResidueFibres_evaluate hG i hi hLf a
      have hc := hclass k A ((baseChange a.left).obj L) (familyHom i a)
        (isClosedSubgroup_familyHom i hi a)
      change (∃ b : A ⟶ U k, evaluate (j k) b = evaluate i a) ↔
        Set.range a.left ⊆ ((V ⊓ W : T.left.Opens) : Set T.left)
      exact (hc.2 hf).trans (((hV A.left a.left).symm.and (hW A a).2.symm).trans
        Set.subset_inter_iff.symm)
  refine torusCentralizerChartGluing (Spec R) G hG I U H j hopens ?_
  intro T L i hi hLs hLg hLf t
  have : Smooth L.X.hom := hLs
  have : GeometricallyConnected L.X.hom := hLg
  obtain ⟨n, r, V, htV, hR, hN⟩ := torusCentralizerJetCoverage R G hG T L i hi hLf t
  let k : I := ⟨(n, r)⟩
  let A := Over.mk (V.ι ≫ T.hom)
  let a : A ⟶ T := Over.homMk V.ι rfl
  have : Smooth ((baseChange a.left).obj L).X.hom :=
    inferInstanceAs (Smooth (pullback.snd L.X.hom a.left))
  have : GeometricallyConnected ((baseChange a.left).obj L).X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd L.X.hom a.left))
  have hp := hclass k A ((baseChange a.left).obj L) (familyHom i a)
    (isClosedSubgroup_familyHom i hi a)
  have hf := centralizerResidueFibres_evaluate hG i hi hLf a
  exact ⟨k, V, htV, (hp.2 hf).mpr ⟨hR, hN⟩⟩

end Langlands.GroupScheme.TorusSubgroupModuli
