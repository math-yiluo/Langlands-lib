import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeAlgebraicClosureInfiniteReduction
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Ranks of closed split tori against a maximal torus of a residue fibre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, a closed split torus of a smooth connected affine group
has at most as many factors as a split maximal torus. -/
theorem card_le_card_of_isMaximalTorus {k : Type u} [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k))) [Smooth H.X.hom] [IsAffineHom H.X.hom]
    [ConnectedSpace H.X.left] {T A : CommGroupScheme (Spec (CommRingCat.of k))}
    {j : T.toGrp ⟶ H} (hj : IsMaximalTorus j) {a : A.toGrp ⟶ H} (ha : IsClosedSubgroup a)
    (I J : Type u) [Finite I] [Finite J]
    (eT : T.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I)
    (eA : A.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) J) : Nat.card J ≤ Nat.card I := by
  have hA : IsTorus A.toGrp :=
    (IsSplitTorus.of_iso eA (isSplitTorus_splitTorus J)).isTorus
  obtain ⟨T', i', f, hi', hf⟩ := EnvelopeInfiniteReduction.exists_isMaximalTorus_factor H a hA ha
  obtain ⟨g, φ, -⟩ := maximalTorusConjugacy k H T' T i' j hi' hj
  have : IsClosedImmersion a.hom.hom.left := ha
  have hma : Mono a.hom.hom := Over.mono_of_mono_left _
  have hmf : Mono f.hom.hom := by
    have h : (f ≫ i').hom.hom = f.hom.hom ≫ i'.hom.hom := rfl
    have : Mono (f.hom.hom ≫ i'.hom.hom) := by rw [← h, hf]; exact hma
    exact mono_of_mono f.hom.hom i'.hom.hom
  have : IsIso eA.inv.hom.hom := inferInstanceAs (IsIso ((Grp.forget _).mapIso eA).inv)
  have : IsIso eT.hom.hom.hom := inferInstanceAs (IsIso ((Grp.forget _).mapIso eT).hom)
  have : IsIso (CommGroupScheme.groupHom φ.hom).hom.hom := by
    let ψ : T'.toGrp ≅ T.toGrp :=
      { hom := CommGroupScheme.groupHom φ.hom
        inv := CommGroupScheme.groupHom φ.inv
        hom_inv_id := congrArg Additive.toMul φ.hom_inv_id
        inv_hom_id := congrArg Additive.toMul φ.inv_hom_id }
    exact inferInstanceAs (IsIso ((Grp.forget _).mapIso ψ).hom)
  let m : splitTorus (Spec (CommRingCat.of k)) J ⟶ splitTorus (Spec (CommRingCat.of k)) I :=
    eA.inv ≫ f ≫ CommGroupScheme.groupHom φ.hom ≫ eT.hom
  have : Mono m.hom.hom := by
    change Mono (eA.inv.hom.hom ≫ f.hom.hom ≫ (CommGroupScheme.groupHom φ.hom).hom.hom ≫
      eT.hom.hom.hom)
    infer_instance
  exact splitTorus.card_le_card_of_mono J I m

/-- Base change around a commutative square of base schemes, as an isomorphism of group
schemes. -/
def baseChangeSquareIso {S S₁ S₂ S₃ : Scheme.{u}} {s : S₁ ⟶ S} {β : S₂ ⟶ S}
    {γ : S₃ ⟶ S₁} {s' : S₃ ⟶ S₂} (h : γ ≫ s = s' ≫ β) (G : GroupScheme S) :
    (baseChange γ).obj ((baseChange s).obj G) ≅ (baseChange s').obj ((baseChange β).obj G) :=
  (baseChangeCompIso s γ G).symm ≪≫ eqToIso (congrArg (fun f => (baseChange f).obj G) h) ≪≫
    baseChangeCompIso β s' G

/-- **Rank comparison on the residue fibre.** Let `M` be a smooth affine group over `Spec O`
whose fibre `M_k` over a field point `s : Spec k ⟶ Spec O` is connected, and let `T₀` be a
closed maximal torus of `M_k`. Let `𝒯` be a group over `Spec O` whose fibre at `s` is
isomorphic to `T₀`. Let `β : Spec O' ⟶ Spec O` be a base change and `s' : Spec k' ⟶ Spec O'` a
point with values in an algebraically closed extension `k'` of `k`, compatible with `s`. If
`𝒯_{O'}` is split with index `I`, then every closed split torus of `M_{O'}` with index `J`
has `|J| ≤ |I|`. -/
theorem card_le_card_of_residue_isMaximalTorus {O O' k k' : Type u} [CommRing O] [CommRing O']
    [Field k] [Field k'] [Algebra k k'] [IsAlgClosed k']
    {s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of O)}
    {β : Spec (CommRingCat.of O') ⟶ Spec (CommRingCat.of O)}
    {s' : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of O')}
    (hsq : Spec.map (CommRingCat.ofHom (algebraMap k k')) ≫ s = s' ≫ β)
    (M : GroupScheme (Spec (CommRingCat.of O))) [Smooth M.X.hom] [IsAffineHom M.X.hom]
    [ConnectedSpace ((baseChange s).obj M).X.left]
    {T₀ : CommGroupScheme (Spec (CommRingCat.of k))} {t₀ : T₀.toGrp ⟶ (baseChange s).obj M}
    (hT : IsTorus T₀.toGrp) (hic : IsClosedSubgroup t₀) (hmax : IsMaximalTorus t₀)
    (𝒯 : GroupScheme (Spec (CommRingCat.of O))) (e : (baseChange s).obj 𝒯 ≅ T₀.toGrp)
    (I : Type u) [Finite I] (eT : (baseChange β).obj 𝒯 ≅ splitTorus (Spec (CommRingCat.of O')) I)
    {𝒜 : CommGroupScheme (Spec (CommRingCat.of O'))} {a : 𝒜.toGrp ⟶ (baseChange β).obj M}
    (ha : IsClosedSubgroup a) (J : Type u) [Finite J]
    (eA : 𝒜.toGrp ≅ splitTorus (Spec (CommRingCat.of O')) J) : Nat.card J ≤ Nat.card I := by
  let γ := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let Mk := (baseChange s).obj M
  have : Smooth Mk.X.hom := inferInstanceAs (Smooth (Limits.pullback.snd M.X.hom s))
  have : IsAffineHom Mk.X.hom := inferInstanceAs (IsAffineHom (Limits.pullback.snd M.X.hom s))
  let H := (baseChange γ).obj Mk
  have : Smooth H.X.hom := inferInstanceAs (Smooth (Limits.pullback.snd Mk.X.hom γ))
  have : IsAffineHom H.X.hom := inferInstanceAs (IsAffineHom (Limits.pullback.snd Mk.X.hom γ))
  have : ConnectedSpace H.X.left := Mk.connectedSpace_baseChange_of_smooth_affine γ
  have hj := (maximalTorusBaseChange k k' Mk T₀ t₀ hT hic).1 hmax
  have ha' : IsClosedSubgroup ((baseChange s').map a ≫ (baseChangeSquareIso hsq M).inv) :=
    (IsClosedSubgroup.baseChange s' ha).comp_iso (baseChangeSquareIso hsq M).symm
  exact card_le_card_of_isMaximalTorus H
    (T := (CommGroupScheme.baseChange γ).obj T₀)
    (A := (CommGroupScheme.baseChange s').obj 𝒜) hj ha' I J
    ((baseChange γ).mapIso e.symm ≪≫ baseChangeSquareIso hsq 𝒯 ≪≫ (baseChange s').mapIso eT ≪≫
      splitTorus.baseChangeIso s' I)
    ((baseChange s').mapIso eA ≪≫ splitTorus.baseChangeIso s' J)

end Langlands.GroupScheme
