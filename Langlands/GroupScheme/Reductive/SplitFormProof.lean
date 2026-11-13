import Langlands.GroupScheme.Reductive.SplitFormStatement
import Langlands.GroupScheme.Reductive.PinnedIsomorphismReduction
import Langlands.GroupScheme.Reductive.SplitIsomorphismProof
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.SplitExistence
import Langlands.GroupScheme.Reductive.RootDatumFieldComparison
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction

/-! # The split form of a reductive group (Milne, Corollary 23.57): proof -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace SplitForm

/-- Two connected reductive groups over a field, with split maximal tori whose root data are
equivalent as root pairings, are isomorphic. The torus isomorphism realizing the weight map of
the equivalence moves the second maximal torus onto the first; the Isomorphism Theorem for a
common split maximal torus then applies. -/
theorem nonempty_iso_of_rootDatumEquiv {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    {i : T.toGrp ⟶ G} {j : T'.toGrp ⟶ H}
    (hi : IsMaximalTorus i) (hj : IsMaximalTorus j)
    {J J' : Type u}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {Q : RootDatum J' (characterLattice T') (cocharacterLattice T')}
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hQ : haveI := hH.isAffineHom; IsRootDatumOf j Q)
    (e : RootPairing.Equiv P Q) : Nonempty (G ≅ H) := by
  let := hG.isAffineHom
  let := hH.isAffineHom
  let t : T ≅ T' := hT.isoOfCharacterEquiv hT' e.weightEquiv.toAddEquiv
  have hR : IsRootDatumOf (CommGroupScheme.groupHom t.hom ≫ j) P :=
    IsRootDatumOf.precomp_torusIso t hQ hP.1 e fun χ =>
      (DFunLike.congr_fun
        (hT.character_congr_isoOfCharacterEquiv hT' e.weightEquiv.toAddEquiv) χ).symm
  have hM : IsMaximalTorus (CommGroupScheme.groupHom t.hom ≫ j) :=
    IsMaximalTorus.precomp_torusIso t hj
  obtain ⟨ψ, -⟩ := splitCommonTorusIsomorphism k G H hG hH T hT i _ hi hM J J P P hP hR
    (Equiv.refl J) rfl rfl
  exact ⟨ψ⟩

end SplitForm

open SplitForm in
/-- **The split form** (Milne, *Algebraic Groups* (2017), Corollary 23.57). -/
theorem splitForm : SplitFormStatement.{u} := by
  intro k _ G hG
  let ks := SeparableClosure k
  let b := algebraBaseMap k ks
  refine ⟨?_, ?_⟩
  · -- Existence: a split form with the root datum of `G_{k_s}`.
    have hGs := connectedReductiveFieldExtensionStatement k ks G hG
    let := hGs.smooth
    let := hGs.isAffineHom
    obtain ⟨Ts, is, his, hTs⟩ :=
      exists_isMaximalTorus_isSplitTorus_of_isSepClosed
        ((GroupScheme.baseChange b).obj G)
    obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence ks _ hGs Ts hTs is his
    have : Module.Finite ℤ (characterLattice Ts) := hTs.finite_characterLattice
    obtain ⟨G₀, hG₀, T₀, i₀, hT₀, hi₀, Q, hQ, ⟨eQ⟩⟩ :=
      splitReductiveExistence k J (characterLattice Ts) (cocharacterLattice Ts) P hred
    refine ⟨G₀, T₀, i₀, hG₀, hT₀, hi₀, ?_⟩
    let := hG₀.smooth
    let := hG₀.isAffineHom
    have hG₀s := connectedReductiveFieldExtensionStatement k ks G₀ hG₀
    have hi₀s := (maximalTorusBaseChange k ks G₀ T₀ i₀ hi₀.1 hi₀.2.1).mp hi₀
    have hQs := splitRootDatumFieldExtension k ks G₀ hG₀ T₀ hT₀ i₀ hi₀ J Q hQ
    exact nonempty_iso_of_rootDatumEquiv hG₀s hGs (hT₀.baseChange b) hTs hi₀s his hQs hP
      ((SplitRootDatum.baseChangeEquiv b T₀ hT₀ Q).comp eQ).symm
  · -- Uniqueness: the root data over `k` become equivalent over `k_s`.
    intro G₁ G₂ T₁ T₂ i₁ i₂ hG₁ hG₂ hT₁ hT₂ hi₁ hi₂ ⟨f₁⟩ ⟨f₂⟩
    let := hG₁.smooth
    let := hG₁.isAffineHom
    let := hG₂.smooth
    let := hG₂.isAffineHom
    obtain ⟨J₁, -, P₁, hP₁, -⟩ := rootDatumExistence k G₁ hG₁ T₁ hT₁ i₁ hi₁
    obtain ⟨J₂, -, P₂, hP₂, -⟩ := rootDatumExistence k G₂ hG₂ T₂ hT₂ i₂ hi₂
    have hG₁s := connectedReductiveFieldExtensionStatement k ks G₁ hG₁
    have hG₂s := connectedReductiveFieldExtensionStatement k ks G₂ hG₂
    have hi₁s := (maximalTorusBaseChange k ks G₁ T₁ i₁ hi₁.1 hi₁.2.1).mp hi₁
    have hi₂s := (maximalTorusBaseChange k ks G₂ T₂ i₂ hi₂.1 hi₂.2.1).mp hi₂
    have hP₁s := splitRootDatumFieldExtension k ks G₁ hG₁ T₁ hT₁ i₁ hi₁ J₁ P₁ hP₁
    have hP₂s := splitRootDatumFieldExtension k ks G₂ hG₂ T₂ hT₂ i₂ hi₂ J₂ P₂ hP₂
    obtain ⟨es⟩ := nonempty_rootDatumEquiv_of_iso hG₁s hG₂s (hT₁.baseChange b)
      (hT₂.baseChange b) hi₁s hi₂s (f₁ ≪≫ f₂.symm) hP₁s hP₂s
    exact nonempty_iso_of_rootDatumEquiv hG₁ hG₂ hT₁ hT₂ hi₁ hi₂ hP₁ hP₂
      ((SplitRootDatum.baseChangeEquiv b T₂ hT₂ P₂).symm.comp
        (es.comp (SplitRootDatum.baseChangeEquiv b T₁ hT₁ P₁)))

end Langlands.GroupScheme
