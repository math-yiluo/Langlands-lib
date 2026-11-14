import Langlands.GroupScheme.Reductive.IdentityComponentLocus
import Langlands.GroupScheme.Reductive.Semisimple

/-! # Statement: reductivity and semisimplicity over a direct limit of rings -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Reductivity over a direct limit of rings** (Conrad, *Reductive group schemes* (2014),
Corollary 3.1.11). Let `A = colim Aᵢ` be the colimit of a directed system of commutative
rings, and let `G₀` be a smooth affine group over `A_{i₀}`. Write `Gᵢ` for its base change to
`Aᵢ` (`i₀ ≤ i`) and `G` for its base change to `A`. Then:

1. the identity components of all geometric fibres of `G` are reductive if and only if the
   same holds for `Gᵢ` for all sufficiently large `i`;
2. `G` is reductive if and only if `Gᵢ` is reductive for all sufficiently large `i`;
3. the identity components of all geometric fibres of `G` are semisimple if and only if the
   same holds for `Gᵢ` for all sufficiently large `i`;
4. `G` is semisimple (reductive with semisimple geometric fibres) if and only if `Gᵢ` is
   semisimple for all sufficiently large `i`. -/
def DirectLimitReductiveStatement : Prop :=
  ∀ (ι : Type u) [Preorder ι] [IsDirected ι (· ≤ ·)] (A : ι ⥤ CommRingCat.{u})
    (c : Cocone A), IsColimit c →
    ∀ (i₀ : ι) (G₀ : GroupScheme (Spec (A.obj i₀))) [Smooth G₀.X.hom] [IsAffineHom G₀.X.hom],
      let Gi : ∀ i : ι, i₀ ≤ i → GroupScheme (Spec (A.obj i)) := fun _ h =>
        (GroupScheme.baseChange (Spec.map (A.map (homOfLE h)))).obj G₀
      let G : GroupScheme (Spec c.pt) := (GroupScheme.baseChange (Spec.map (c.ι.app i₀))).obj G₀
      haveI : ∀ i (h : i₀ ≤ i), Smooth (Gi i h).X.hom := fun _ h =>
        inferInstanceAs (Smooth (pullback.snd G₀.X.hom (Spec.map (A.map (homOfLE h)))))
      haveI : ∀ i (h : i₀ ≤ i), IsAffineHom (Gi i h).X.hom := fun _ h =>
        inferInstanceAs (IsAffineHom (pullback.snd G₀.X.hom (Spec.map (A.map (homOfLE h)))))
      haveI : Smooth G.X.hom :=
        inferInstanceAs (Smooth (pullback.snd G₀.X.hom (Spec.map (c.ι.app i₀))))
      haveI : IsAffineHom G.X.hom :=
        inferInstanceAs (IsAffineHom (pullback.snd G₀.X.hom (Spec.map (c.ι.app i₀))))
      let Eventually : (∀ i : ι, i₀ ≤ i → Prop) → Prop := fun p =>
        ∃ i₁ : ι, i₀ ≤ i₁ ∧ ∀ (i : ι) (h : i₀ ≤ i), i₁ ≤ i → p i h
      let SemisimpleFibres : ∀ {S : Scheme.{u}} (H : GroupScheme S) [Smooth H.X.hom]
          [IsAffineHom H.X.hom], Prop := fun {S} H _ _ =>
        ∀ s : S,
          haveI : Smooth (geometricFiber H s).X.hom :=
            inferInstanceAs (Smooth (pullback.snd H.X.hom (geometricPoint S s)))
          haveI : IsAffineHom (geometricFiber H s).X.hom :=
            inferInstanceAs (IsAffineHom (pullback.snd H.X.hom (geometricPoint S s)))
          IsSemisimple (identityComponent (geometricFiber H s))
      (identityComponentReductiveLocus G = Set.univ ↔
        Eventually fun i h => identityComponentReductiveLocus (Gi i h) = Set.univ) ∧
      (IsReductive G ↔ Eventually fun i h => IsReductive (Gi i h)) ∧
      (SemisimpleFibres G ↔ Eventually fun i h => SemisimpleFibres (Gi i h)) ∧
      ((IsReductive G ∧ ∀ s, IsSemisimple (geometricFiber G s)) ↔
        Eventually fun i h =>
          IsReductive (Gi i h) ∧ ∀ s, IsSemisimple (geometricFiber (Gi i h) s))

end Langlands.GroupScheme
