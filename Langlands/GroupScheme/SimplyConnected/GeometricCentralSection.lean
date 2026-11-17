import Langlands.GroupScheme.SimplyConnected.CentralReductiveSection
import Langlands.GroupScheme.SimplyConnected.CentralSectionDescent
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.FactoredKernel

/-! # A central section from a geometric reductive lift -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

section ArbitraryBase

variable {S : Scheme.{u}} {D H G : GroupScheme S}

/-- Restricting a homomorphism to a monic subgroup preserves centrality of its
full scheme-theoretic kernel. -/
theorem IsCentral.kernel_comp {q : H ⟶ G}
    (hq : IsCentral (kernelι q)) (i : D ⟶ H) [Mono i.hom.hom] :
    IsCentral (kernelι (i ≫ q)) := by
  apply IsCentral.of_comp (j := i) inferInstance
  have hc := hq.comp (FactoredKernel.map (i ≫ q) i q rfl)
  simpa only [FactoredKernel.map_comp] using hc

end ArbitraryBase

section Field

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom]
  (hG : IsSimplyConnected G) (q : H ⟶ G) (hq : IsCentral (kernelι q))
  (D : GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k))))
  (i : D ⟶ (baseChange (toAlgebraicClosure k)).obj H)
  [Mono i.hom.hom] (hD : IsConnectedReductive D)
  [Surjective (i ≫ (baseChange (toAlgebraicClosure k)).map q).hom.hom.left]

include hG hq hD i

/-- A central extension has a section over the original field if, over an
algebraic closure, it has a connected reductive monic subgroup surjecting
onto the simply connected target. -/
theorem IsSimplyConnected.exists_section_of_geometric_reductive_lift :
    ∃ s : G ⟶ H, s ≫ q = 𝟙 G := by
  let b := toAlgebraicClosure k
  let B := baseChange b
  have hGK : IsSimplyConnected (B.obj G) :=
    isSimplyConnectedFieldExtension k (AlgebraicClosure k) G hG
  have hqK : IsCentral (kernelι (B.map q)) := hq.kernel_baseChange b
  obtain ⟨sK, hsK⟩ :=
    hGK.exists_section_of_central_reductive hD (i ≫ B.map q) (hqK.kernel_comp i)
  have hs : (sK ≫ i) ≫ B.map q = 𝟙 (B.obj G) := by
    simpa only [Category.assoc] using hsK
  let : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
  have hff : Flat b ∧ Surjective b :=
    (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let : Flat b := hff.1
  let : Surjective b := hff.2
  exact CentralSectionDescent.exists_section q hq
    (semisimplePerfect k G hG.isSemisimple) b (sK ≫ i) hs

/-- The section over the original field obtained from a supplied geometric
connected reductive lift of the quotient. -/
def IsSimplyConnected.geometricCentralSection : G ⟶ H :=
  (hG.exists_section_of_geometric_reductive_lift q hq D i hD).choose

/-- The constructed homomorphism is a section over the original field. -/
@[reassoc]
theorem IsSimplyConnected.geometricCentralSection_comp :
    hG.geometricCentralSection q hq D i hD ≫ q = 𝟙 G :=
  (hG.exists_section_of_geometric_reductive_lift q hq D i hD).choose_spec

end Field

end Langlands.GroupScheme
