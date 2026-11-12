import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Derived.Basic

/-! # The semisimple anisotropic kernel of an actual Tits index: statements -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G D : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]

/-- Index data `e` of a group `D` mapped to `G` by `ι` realizes the subdiagram of
`d` on `Δ₀`: a `k`-torus map carries the maximal torus of `e` into that of `d`
compatibly with `ι`, and the absolute roots of `e` correspond bijectively to the
absolute roots of `d` with zero restriction to the maximal split torus, by actual
character restriction and cocharacter pushforward along this torus map. The
correspondence preserves root pairings, carries the base of `e` onto `Δ₀`, and
intertwines the full star actions on simple vertices. -/
def TitsIndexData.KernelComparison (d : TitsIndexData G) (ι : D ⟶ G)
    (e : TitsIndexData D) : Prop :=
  ∃ (τ : e.pinning.torus ⟶ d.pinning.torus)
    (φ : e.pinning.rootIndex ≃ {a : d.pinning.rootIndex // d.rootRestriction a = 0}),
    CommGroupScheme.groupHom τ ≫ d.pinning.inclusion = e.pinning.inclusion ≫ ι ∧
    (∀ b, e.pinning.rootDatum.root b =
      (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map τ ≫
        d.pinning.rootDatum.root (φ b).val) ∧
    (∀ b, e.pinning.rootDatum.coroot b ≫
      (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map τ =
        d.pinning.rootDatum.coroot (φ b).val) ∧
    (∀ b c, e.pinning.rootDatum.pairing b c =
      d.pinning.rootDatum.pairing (φ b).val (φ c).val) ∧
    (∀ b, b ∈ e.pinning.base.support ↔ (φ b).val ∈ d.pinning.base.support) ∧
    (∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) b, b ∈ e.pinning.base.support →
      (φ ((e.pinning.starAction σ).val.indexEquiv b)).val =
        (d.pinning.starAction σ).val.indexEquiv (φ b).val)

/-- For actual index data `d` of `G`, every actual derived subgroup `D` of every
actual representative `M` of the centralizer of the chosen maximal split torus is
semisimple and anisotropic. -/
def TitsAnisotropicKernelStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
    (torusCentralizer d.splitInclusion).IsRepresentedBy j →
    ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (i : D ⟶ M),
      IsDerivedSubgroup i → IsSemisimple D ∧ IsAnisotropic D

/-- For actual index data `d` of `G`, every actual derived subgroup `D` of every
actual representative `M` of the centralizer of the chosen maximal split torus is
affine and locally of finite type, and has actual index data whose index is the
subdiagram of `d` on `Δ₀` along the composite inclusion `D ⟶ M ⟶ G`. -/
def TitsAnisotropicKernelIndexStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
    (torusCentralizer d.splitInclusion).IsRepresentedBy j →
    ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (i : D ⟶ M),
      IsDerivedSubgroup i →
        ∃ (_ : IsAffineHom D.X.hom) (_ : LocallyOfFiniteType D.X.hom)
          (e : TitsIndexData D), d.KernelComparison (i ≫ j) e

/-- The two anisotropic-kernel assertions of Tits §§2.2–2.3, retained as
unproved proposition definitions. -/
def TitsAnisotropicKernelStructureStatement : Prop :=
  TitsAnisotropicKernelStatement.{u} ∧ TitsAnisotropicKernelIndexStatement.{u}

end Langlands.GroupScheme
