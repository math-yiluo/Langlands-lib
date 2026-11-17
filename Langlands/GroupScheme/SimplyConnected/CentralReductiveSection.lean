import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.CentralSurjection.DerivedMap
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Derived.SemisimpleProof

/-! # Sections of central surjections onto simply connected semisimple groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A central surjection from a connected reductive group onto a simply connected
semisimple group has a homomorphic section. -/
theorem IsSimplyConnected.exists_section_of_central_reductive
    (hG : IsSimplyConnected G) (hH : IsConnectedReductive H)
    (q : H ⟶ G) [Surjective q.hom.hom.left]
    (hq : IsCentral (kernelι q)) :
    ∃ s : G ⟶ H, s ≫ q = 𝟙 G := by
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : Smooth H.X.hom := hH.smooth
  obtain ⟨D, d, _, _, hd⟩ := derivedSubgroupRepresentability k H
  have hid : IsDerivedSubgroup (𝟙 G) :=
    ⟨(derivedSubgroup_total_admissible G).1,
      (SubgroupFunctor.range_id G).trans (semisimplePerfect k G hG.isSemisimple).symm⟩
  let m : D ⟶ G := hd.map hid q
  have hm : IsCentralIsogeny m :=
    hd.isCentralIsogeny_map hid q hH hG.isSemisimple.isConnectedReductive hq
  let : IsIso m := hG.central_isogeny_isIso D m
    (derivedSubgroupSemisimple k H D d hH hd) hm
  refine ⟨inv m ≫ d, ?_⟩
  have hcomp : d ≫ q = m := by
    simpa only [Category.comp_id] using (hd.map_comp hid q).symm
  rw [Category.assoc, hcomp, IsIso.inv_hom_id]

/-- A chosen homomorphic section of a central surjection from a connected reductive
group onto a simply connected semisimple group. -/
def IsSimplyConnected.centralReductiveSection
    (hG : IsSimplyConnected G) (hH : IsConnectedReductive H)
    (q : H ⟶ G) [Surjective q.hom.hom.left]
    (hq : IsCentral (kernelι q)) : G ⟶ H :=
  (hG.exists_section_of_central_reductive hH q hq).choose

/-- The chosen section is a right inverse to the quotient homomorphism. -/
@[reassoc]
theorem IsSimplyConnected.centralReductiveSection_comp
    (hG : IsSimplyConnected G) (hH : IsConnectedReductive H)
    (q : H ⟶ G) [Surjective q.hom.hom.left]
    (hq : IsCentral (kernelι q)) :
    hG.centralReductiveSection hH q hq ≫ q = 𝟙 G :=
  (hG.exists_section_of_central_reductive hH q hq).choose_spec

end Langlands.GroupScheme
