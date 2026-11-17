import Langlands.GroupScheme.Torus.MultiplicativeTypeArtinianCentralityReduction
import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralRigidityStatement
import Langlands.GroupScheme.HomScheme.ConjugationMap
import Langlands.GroupScheme.FppfHomLocality
import Langlands.GroupScheme.Rational.CentralTorusFixedness
import Langlands.GroupScheme.IntegralModel

/-! # Fibrewise centrality from central rigidity -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.MultiplicativeTypeFibrewiseCentralityReduction

open HomScheme MultiplicativeTypeAffineInfinitesimalCentrality
  MultiplicativeTypeArtinianCentralityReduction

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- Central rigidity and Zariski locality detect equality of homomorphisms
whose residue fibres agree and are central. -/
theorem hom_eq_of_central_fibres
    (hRig : MultiplicativeTypeCentralRigidityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated G.X.hom] (f g : H ⟶ G)
    (he : ∀ s : S, (baseChange (S.fromSpecResidueField s)).map f =
      (baseChange (S.fromSpecResidueField s)).map g)
    (hc : ∀ s : S, IsCentral ((baseChange (S.fromSpecResidueField s)).map f)) :
    f = g := by
  apply hom_ext_of_pointwise_fppf_baseChange
  intro s
  obtain ⟨U, hs, hU⟩ :=
    (hRig S H G hH (Or.inr ⟨inferInstance, inferInstance, inferInstance⟩)).1 f g s
      (he s) (hc s)
  exact ⟨U, U.ι, inferInstance, inferInstance, ⟨⟨s, hs⟩, rfl⟩, hU⟩

/-- Equality of relative evaluations is equality of the underlying iterated
base changes, because the direct/iterated comparisons are isomorphisms. -/
theorem baseChange_eq_of_evaluate_eq {M T : Over S} (a : T ⟶ M)
    {f g : RelativeHom H G M} (he : evaluate a f = evaluate a g) :
    (baseChange a.left).map f = (baseChange a.left).map g := by
  let eH := Descent.pullbackComparison M.hom a.left T.hom (Over.w a) H
  let eG := Descent.pullbackComparison M.hom a.left T.hom (Over.w a) G
  apply (cancel_epi eH.inv).mp
  apply (cancel_mono eG.hom).mp
  simpa only [evaluate, Descent.pullHom, Category.assoc, eH, eG] using he

/-- A conjugation family agrees with the constant family on each residue
fibre whenever the original homomorphism has central residue fibres. -/
theorem conjugationFamily_fibre_eq (i : H ⟶ G)
    (hc : ∀ s : S, IsCentral ((baseChange (S.fromSpecResidueField s)).map i))
    (T : Over S) (g : T ⟶ G.X) (t : T.left) :
    (baseChange (T.left.fromSpecResidueField t)).map (conjugationFamily i g) =
      (baseChange (T.left.fromSpecResidueField t)).map ((baseChange T.hom).map i) := by
  let a : Over.mk (T.left.fromSpecResidueField t ≫ T.hom) ⟶ T :=
    Over.homMk (T.left.fromSpecResidueField t) rfl
  apply baseChange_eq_of_evaluate_eq a
  rw [evaluate_conjugationFamily, evaluate_baseChange]
  exact (isCentral_field_baseChange i hc (T.left.residueField t)
    (T.left.fromSpecResidueField t ≫ T.hom)).comp_innerIso_hom _

/-- Central rigidity makes every conjugation family of a fibrewise central
homomorphism constant. -/
theorem conjugationFamily_eq_of_fibres
    (hRig : MultiplicativeTypeCentralRigidityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated G.X.hom] (i : H ⟶ G)
    (hc : ∀ s : S, IsCentral ((baseChange (S.fromSpecResidueField s)).map i))
    (T : Over S) (g : T ⟶ G.X) :
    conjugationFamily i g = (baseChange T.hom).map i := by
  have : LocallyOfFinitePresentation ((baseChange T.hom).obj G).X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom T.hom))
  have : QuasiCompact ((baseChange T.hom).obj G).X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd G.X.hom T.hom))
  have : QuasiSeparated ((baseChange T.hom).obj G).X.hom :=
    inferInstanceAs (QuasiSeparated (pullback.snd G.X.hom T.hom))
  apply (hom_eq_of_central_fibres hRig (hH.baseChange T.hom)
    ((baseChange T.hom).map i) (conjugationFamily i g) ?_ ?_).symm
  · intro t
    exact (conjugationFamily_fibre_eq i hc T g t).symm
  · intro t
    apply (isCentral_baseChange_comp_iff T.hom (T.left.fromSpecResidueField t) i).mp
    exact isCentral_field_baseChange i hc (T.left.residueField t)
      (T.left.fromSpecResidueField t ≫ T.hom)

/-- A conjugation-family equality implies commutation of the original
test-scheme points. -/
theorem commute_of_conjugationFamily_eq (i : H ⟶ G) {T : Over S}
    (x : T ⟶ H.X) (g : T ⟶ G.X)
    (he : conjugationFamily i g = (baseChange T.hom).map i) :
    Commute (x ≫ i.hom.hom) g := by
  let x' := RelativeLevi.pulledBackPoint H T x
  let g' := RelativeLevi.pulledBackPoint G T g
  have hp := congrArg
    (fun f : (baseChange T.hom).obj H ⟶ (baseChange T.hom).obj G =>
      x' ≫ f.hom.hom) he
  change x' ≫ ((baseChange T.hom).map i).hom.hom ≫
    ((((baseChange T.hom).obj G).innerIso g').hom).hom.hom =
      x' ≫ ((baseChange T.hom).map i).hom.hom at hp
  rw [← Category.assoc, comp_innerIso_hom] at hp
  have hconst : ((baseChange T.hom).obj G).constantPoint g' (Over.mk (𝟙 T.left)) = g' := by
    change (𝟙 (Over.mk (𝟙 T.left))) ≫ g' = g'
    exact Category.id_comp _
  rw [hconst] at hp
  have hp' := congrArg (baseChangeBasePointsEquiv T.hom G) hp
  rw [map_mul, map_mul, map_inv, baseChangeBasePointsEquiv_comp,
    RelativeLevi.baseChangeBasePointsEquiv_pulledBackPoint,
    RelativeLevi.baseChangeBasePointsEquiv_pulledBackPoint] at hp'
  exact (mul_inv_eq_iff_eq_mul.mp hp').symm

/-- Central rigidity implies the arbitrary-base fibrewise detection clause. -/
theorem isCentral_of_fibres_of_centralRigidity
    (hRig : MultiplicativeTypeCentralRigidityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated G.X.hom] (i : H ⟶ G)
    (hc : ∀ s : S, IsCentral ((baseChange (S.fromSpecResidueField s)).map i)) :
    IsCentral i := by
  intro T x
  apply mem_center.mpr
  intro T' a g
  simpa only [Category.assoc] using
    commute_of_conjugationFamily_eq i (a ≫ x) g
      (conjugationFamily_eq_of_fibres hRig hH i hc T' g)

/-- Centrality of the residue fibre at the image of a parameter point gives
centrality of the constant family's residue fibre there. -/
theorem isCentral_constantFamily_fibre (i : H ⟶ G) (T : Over S) (t : T.left)
    (hc : IsCentral ((baseChange (S.fromSpecResidueField (T.hom t))).map i)) :
    IsCentral ((baseChange (T.left.fromSpecResidueField t)).map
      ((baseChange T.hom).map i)) := by
  apply (isCentral_baseChange_comp_iff T.hom (T.left.fromSpecResidueField t) i).mp
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField T.hom t]
  exact (isCentral_baseChange_comp_iff _ _ i).mpr
    (hc.baseChange (Spec.map (T.hom.residueFieldMap t)))

/-- The same single-fibre hypothesis gives equality of the conjugation and
constant families on the parameter's residue fibre. -/
theorem conjugationFamily_fibre_eq_of_isCentral (i : H ⟶ G)
    (T : Over S) (g : T ⟶ G.X) (t : T.left)
    (hc : IsCentral ((baseChange (S.fromSpecResidueField (T.hom t))).map i)) :
    (baseChange (T.left.fromSpecResidueField t)).map (conjugationFamily i g) =
      (baseChange (T.left.fromSpecResidueField t)).map ((baseChange T.hom).map i) := by
  let a : Over.mk (T.left.fromSpecResidueField t ≫ T.hom) ⟶ T :=
    Over.homMk (T.left.fromSpecResidueField t) rfl
  apply baseChange_eq_of_evaluate_eq a
  rw [evaluate_conjugationFamily, evaluate_baseChange]
  have hcf := (isCentral_baseChange_comp_iff T.hom
    (T.left.fromSpecResidueField t) i).mpr (isCentral_constantFamily_fibre i T t hc)
  exact hcf.comp_innerIso_hom _

/-- A central residue fibre gives an actual open neighbourhood of every point
above it on which universal conjugation agrees with the constant family. -/
theorem exists_centralizingOpenAt
    (hRig : MultiplicativeTypeCentralRigidityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated G.X.hom] (i : H ⟶ G) (t : G.X.left)
    (hc : IsCentral ((baseChange (S.fromSpecResidueField (G.X.hom t))).map i)) :
    ∃ W : G.X.left.Opens, t ∈ W ∧
      (baseChange W.ι).map (conjugationFamily i (𝟙 G.X)) =
        (baseChange W.ι).map ((baseChange G.X.hom).map i) := by
  have : LocallyOfFinitePresentation ((baseChange G.X.hom).obj G).X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom G.X.hom))
  have : QuasiCompact ((baseChange G.X.hom).obj G).X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd G.X.hom G.X.hom))
  have : QuasiSeparated ((baseChange G.X.hom).obj G).X.hom :=
    inferInstanceAs (QuasiSeparated (pullback.snd G.X.hom G.X.hom))
  obtain ⟨W, ht, hW⟩ := (hRig G.X.left
    ((baseChange G.X.hom).obj H) ((baseChange G.X.hom).obj G)
    (hH.baseChange G.X.hom) (Or.inr ⟨inferInstance, inferInstance, inferInstance⟩)).1
      ((baseChange G.X.hom).map i) (conjugationFamily i (𝟙 G.X)) t
      (conjugationFamily_fibre_eq_of_isCentral i G.X (𝟙 G.X) t hc).symm
      (isCentral_constantFamily_fibre i G.X t hc)
  exact ⟨W, ht, hW.symm⟩

/-- A chosen centralizing open neighbourhood of a point above a central fibre. -/
def centralizingOpenAt
    (hRig : MultiplicativeTypeCentralRigidityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated G.X.hom] (i : H ⟶ G) (t : G.X.left)
    (hc : IsCentral ((baseChange (S.fromSpecResidueField (G.X.hom t))).map i)) :
    G.X.left.Opens :=
  (exists_centralizingOpenAt hRig hH i t hc).choose

theorem mem_centralizingOpenAt
    (hRig : MultiplicativeTypeCentralRigidityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated G.X.hom] (i : H ⟶ G) (t : G.X.left)
    (hc : IsCentral ((baseChange (S.fromSpecResidueField (G.X.hom t))).map i)) :
    t ∈ centralizingOpenAt hRig hH i t hc :=
  (exists_centralizingOpenAt hRig hH i t hc).choose_spec.1

theorem centralizingOpenAt_eq
    (hRig : MultiplicativeTypeCentralRigidityStatement.{u})
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    [QuasiSeparated G.X.hom] (i : H ⟶ G) (t : G.X.left)
    (hc : IsCentral ((baseChange (S.fromSpecResidueField (G.X.hom t))).map i)) :
    (baseChange (centralizingOpenAt hRig hH i t hc).ι).map (conjugationFamily i (𝟙 G.X)) =
      (baseChange (centralizingOpenAt hRig hH i t hc).ι).map
        ((baseChange G.X.hom).map i) :=
  (exists_centralizingOpenAt hRig hH i t hc).choose_spec.2

end Langlands.GroupScheme.MultiplicativeTypeFibrewiseCentralityReduction
