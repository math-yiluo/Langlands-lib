import Langlands.GroupScheme.Reductive.AffinePinnedModel
import Langlands.GroupScheme.Reductive.EtaleLocalSplitProof
import Langlands.LinearAlgebra.RootDatumBaseExists
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Cover.Sigma

/-! # Affine pinned étale charts of an arbitrary reductive group scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- A supplied affine pinned model identified with the actual pullback of a
group scheme along an étale chart. -/
structure AffinePinnedChart {S : Scheme.{u}} (G : GroupScheme S) where
  model : AffinePinnedModel.{u}
  map : model.base ⟶ S
  etale : Etale map
  iso : (GroupScheme.baseChange map).obj G ≅ model.group

namespace AffinePinnedChart

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Every point of the base of a reductive group is covered by an affine
pinned étale chart. The pinning is chosen from the free root lines. -/
theorem exists_over (hG : IsReductive G) (s : S) :
    ∃ C : AffinePinnedChart G, ∃ x : C.model.base, C.map x = s := by
  classical
  let := hG.isAffineHom
  obtain ⟨R, hR, f, hf, hx, I, hI, i, hi, hmax, J, P, hP, hlines⟩ :=
    etaleLocalSplitReductive S G hG s
  let : CommRing R := hR
  let : Fintype I := hI
  let H := (GroupScheme.baseChange f).obj G
  have hH : IsReductive H := hG.baseChange f
  let := hH.isAffineHom
  let : Finite J := hP.finite
  let : Fintype J := Fintype.ofFinite J
  let : P.IsReduced := hP.isReduced
  let b : P.Base := Langlands.LinearAlgebra.RootDatumBase.base P
  let M : AffinePinnedModel.{u} :=
    { ring := R
      group := H
      reductive := hH
      coordinates := I
      inclusion := i
      closed := hi
      maximal := hmax
      rootIndex := J
      rootDatum := P
      fibrewiseRootDatum := hP
      rootLines := hlines
      basis := b
      pinning := fun a => (Classical.choice (hlines a)).symm }
  exact ⟨⟨M, f, hf, Iso.refl H⟩, hx⟩

end AffinePinnedChart

/-- A point-indexed family of affine pinned étale charts covering the base.
The distinguished point witnesses coverage without any finiteness hypothesis. -/
structure AffinePinnedAtlas {S : Scheme.{u}} (G : GroupScheme S) where
  chart : S → AffinePinnedChart G
  point : ∀ s : S, (chart s).model.base
  image_point : ∀ s : S, (chart s).map (point s) = s

namespace AffinePinnedAtlas

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Choose a pinned affine chart above each point using the proved étale local
splitting theorem. -/
def ofReductive (hG : IsReductive G) : AffinePinnedAtlas G where
  chart s := Classical.choose (AffinePinnedChart.exists_over hG s)
  point s := Classical.choose (Classical.choose_spec (AffinePinnedChart.exists_over hG s))
  image_point s := Classical.choose_spec
    (Classical.choose_spec (AffinePinnedChart.exists_over hG s))

variable (A : AffinePinnedAtlas G)

/-- The actual étale covering family supplied by the atlas. -/
def cover : S.Cover Scheme.etalePrecoverage :=
  Scheme.Cover.mkOfCovers S (fun s => (A.chart s).model.base)
    (fun s => (A.chart s).map)
    (fun s => ⟨s, A.point s, A.image_point s⟩)
    (fun s => (A.chart s).etale)

/-- The disjoint union of all the pinned affine charts. -/
abbrev space : Scheme.{u} := ∐ fun s : S => (A.chart s).model.base

/-- The actual single covering morphism of the atlas. -/
def projection : A.space ⟶ S := Sigma.desc fun s => (A.chart s).map

instance : Etale A.projection :=
  (A.cover.sigma.map_prop PUnit.unit)

instance : Surjective A.projection := by
  constructor
  intro s
  exact ⟨Sigma.ι (fun t : S => (A.chart t).model.base) s (A.point s), by
    simpa only [projection, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc] using A.image_point s⟩

end AffinePinnedAtlas

end Langlands.GroupScheme
