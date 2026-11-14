import Langlands.GroupScheme.Torus.IdentityTransporterEtaleLift
import Langlands.GroupScheme.HomConjugacy
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Etale conjugacy of dynamic parabolics from a prescribed fibre transporter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace PointwiseSchemeAction

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- An all-test transporter at the terminal test scheme is the corresponding
equality of homomorphisms under the prescribed inner automorphism. -/
theorem IsTransporter.comp_innerIso_eq {χ ψ : H ⟶ G}
    {g : Over.mk (𝟙 S) ⟶ G.X} (hg : IsTransporter ψ χ g) :
    χ ≫ (G.innerIso g).hom = ψ := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
  let a : T ⟶ Over.mk (𝟙 S) := Over.homMk T.hom (by simp)
  have h := hg T a x
  change (x ≫ ψ.hom.hom) * G.constantPoint g T =
    G.constantPoint g T * (x ≫ χ.hom.hom) at h
  rw [← h, mul_inv_cancel_right]

/-- Transfer the pointed diagonalizable transporter lift along an actual
source isomorphism, obtaining an equality of actual homomorphisms. -/
theorem exists_pointed_etale_hom_conjugacy
    {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
    [IsAffine G.X.left] (hG : Smooth G.X.hom)
    {M : Type u} [AddCommGroup M]
    (e : (Diagonalizable.groupScheme R M).toGrp ≅ H)
    (χ ψ : H ⟶ G) (s : Spec R)
    (g₀ : Over.mk (𝟙 (Spec ((Spec R).residueField s))) ⟶
      ((baseChange ((Spec R).fromSpecResidueField s)).obj G).X)
    (hg₀ : IsTransporter
      ((baseChange ((Spec R).fromSpecResidueField s)).map ψ)
      ((baseChange ((Spec R).fromSpecResidueField s)).map χ) g₀) :
    ∃ (U : Scheme.{u}) (p : U ⟶ Spec R), Etale p ∧
      ∃ (b : Spec ((Spec R).residueField s) ⟶ U),
        b ≫ p = (Spec R).fromSpecResidueField s ∧
        ∃ g : Over.mk (𝟙 U) ⟶ ((baseChange p).obj G).X,
          (baseChange p).map χ ≫ (((baseChange p).obj G).innerIso g).hom =
            (baseChange p).map ψ ∧
          b ≫ g.left ≫ Limits.pullback.fst G.X.hom p =
            g₀.left ≫ Limits.pullback.fst G.X.hom ((Spec R).fromSpecResidueField s) := by
  let c := (Spec R).fromSpecResidueField s
  have hpre : IsTransporter ((baseChange c).map (e.hom ≫ ψ))
      ((baseChange c).map (e.hom ≫ χ)) g₀ := by
    simpa only [Functor.map_comp] using hg₀.precomp ((baseChange c).map e.hom)
  let a₀ := baseChangePointsEquiv c G _ g₀
  have ha₀ : IsTransporter (e.hom ≫ ψ) (e.hom ≫ χ) a₀ :=
    hpre.baseChangePointsEquiv c
  let d := pointedEtaleTransporter (e.hom ≫ ψ) (e.hom ≫ χ) hG s a₀ ha₀
  have hd : IsTransporter ((baseChange d.projection).map ψ)
      ((baseChange d.projection).map χ) d.baseChangedSection := by
    have h := d.baseChangedSection_isTransporter.precomp
      ((baseChange d.projection).map e.inv)
    simpa only [Functor.map_comp, ← Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id, Category.id_comp] using h
  refine ⟨d.neighbourhood, d.projection, d.etale, d.residuePoint, d.residue_over,
    d.baseChangedSection, hd.comp_innerIso_eq, ?_⟩
  exact d.baseChangedSection_recovers

end PointwiseSchemeAction

namespace Dynamic

variable {S : Scheme.{u}} {G P Q : GroupScheme S}

/-- An actual conjugacy of presenting cocharacters conjugates the images of
the represented dynamic parabolics on every test scheme. -/
theorem range_comp_innerIso_eq_of_presentations
    (i : P ⟶ G) (j : Q ⟶ G) (χ ψ : (Gm S).toGrp ⟶ G)
    (hi : SubgroupFunctor.range i = parabolic χ)
    (hj : SubgroupFunctor.range j = parabolic ψ)
    (g : Over.mk (𝟙 S) ⟶ G.X)
    (hχψ : χ ≫ (G.innerIso g).hom = ψ) :
    SubgroupFunctor.range (i ≫ (G.innerIso g).hom) = SubgroupFunctor.range j := by
  let e := G.innerIso g
  have hpar : parabolic χ = (parabolic ψ).comap e.hom := by
    rw [← hχψ]
    exact parabolic_eq_comap_of_iso χ e
  ext T x
  constructor
  · rw [SubgroupFunctor.mem_range]
    rintro ⟨y, rfl⟩
    have hy : y ≫ i.hom.hom ∈ (parabolic χ).carrier T := by
      rw [← hi]
      exact ⟨y, rfl⟩
    rw [hpar, SubgroupFunctor.mem_comap, ← hj] at hy
    simpa only [Grp.comp_hom_hom, Category.assoc] using hy
  · intro hx
    let y : T ⟶ G.X := x ≫ e.inv.hom.hom
    have hy : y ∈ (SubgroupFunctor.range i).carrier T := by
      rw [hi, hpar, SubgroupFunctor.mem_comap]
      have hxy : y ≫ e.hom.hom.hom = x := by
        dsimp [y]
        rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
          Grp.id_hom_hom, Category.comp_id]
      rw [hxy, ← hj]
      exact hx
    rw [SubgroupFunctor.mem_range] at hy ⊢
    obtain ⟨z, hz⟩ := hy
    refine ⟨z, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hz]
    dsimp [y]
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id]

/-- For two globally presented dynamic parabolics over an affine base,
a prescribed residue-field transporter between the cocharacters yields
etale local conjugacy of their actual subgroup images. -/
theorem exists_etale_conjugacy_of_presentations
    {R : CommRingCat.{u}} {G P Q : GroupScheme (Spec R)}
    [IsAffine G.X.left] (hG : Smooth G.X.hom)
    (i : P ⟶ G) (j : Q ⟶ G)
    (χ ψ : (Gm (Spec R)).toGrp ⟶ G)
    (hi : SubgroupFunctor.range i = parabolic χ)
    (hj : SubgroupFunctor.range j = parabolic ψ) (s : Spec R)
    (g₀ : Over.mk (𝟙 (Spec ((Spec R).residueField s))) ⟶
      ((baseChange ((Spec R).fromSpecResidueField s)).obj G).X)
    (hg₀ : PointwiseSchemeAction.IsTransporter
      ((baseChange ((Spec R).fromSpecResidueField s)).map ψ)
      ((baseChange ((Spec R).fromSpecResidueField s)).map χ) g₀) :
    ∃ (U : Scheme.{u}) (p : U ⟶ Spec R), Etale p ∧
      (∃ x : U, p.base x = s) ∧
      ∃ g : Over.mk (𝟙 U) ⟶ ((baseChange p).obj G).X,
        SubgroupFunctor.range ((baseChange p).map i ≫
          (((baseChange p).obj G).innerIso g).hom) =
            SubgroupFunctor.range ((baseChange p).map j) := by
  let e : (Diagonalizable.groupScheme R (PUnit.{u+1} → ℤ)).toGrp ≅
      (Gm (Spec R)).toGrp :=
    Diagonalizable.splitIso R (AddEquiv.refl (PUnit.{u+1} → ℤ)) ≪≫
      (splitTorus.gmIso (Spec R)).symm
  obtain ⟨U, p, hp, b, hb, g, hg, -⟩ :=
    PointwiseSchemeAction.exists_pointed_etale_hom_conjugacy hG e χ ψ s g₀ hg₀
  have hχψ : baseChangeCocharacter p χ ≫ (((baseChange p).obj G).innerIso g).hom =
      baseChangeCocharacter p ψ := by
    simpa only [baseChangeCocharacter, Category.assoc] using
      congrArg (fun f => (Gm.baseChangeIso p).inv ≫ f) hg
  have hi' : SubgroupFunctor.range ((baseChange p).map i) =
      parabolic (baseChangeCocharacter p χ) := by
    rw [SubgroupFunctor.range_baseChangeHom, hi, parabolic_baseChange]
  have hj' : SubgroupFunctor.range ((baseChange p).map j) =
      parabolic (baseChangeCocharacter p ψ) := by
    rw [SubgroupFunctor.range_baseChangeHom, hj, parabolic_baseChange]
  refine ⟨U, p, hp, ⟨b default, ?_⟩, g,
    range_comp_innerIso_eq_of_presentations _ _ _ _ hi' hj' g hχψ⟩
  change (b ≫ p) default = s
  rw [hb, Scheme.fromSpecResidueField_apply]

/-- Etale local conjugacy data for the images of two homomorphisms. -/
structure EtaleSubgroupConjugacyData
    {S : Scheme.{u}} {G P Q : GroupScheme S}
    (i : P ⟶ G) (j : Q ⟶ G) (s : S) where
  neighbourhood : Scheme.{u}
  projection : neighbourhood ⟶ S
  etale : Etale projection
  point : neighbourhood
  point_over : projection.base point = s
  conjugator : Over.mk (𝟙 neighbourhood) ⟶ ((baseChange projection).obj G).X
  conjugates : SubgroupFunctor.range ((baseChange projection).map i ≫
    (((baseChange projection).obj G).innerIso conjugator).hom) =
      SubgroupFunctor.range ((baseChange projection).map j)

/-- Choose etale conjugacy data from global dynamic presentations and a
prescribed residue transporter between their presenting cocharacters. -/
def etaleConjugacyOfPresentations
    {R : CommRingCat.{u}} {G P Q : GroupScheme (Spec R)}
    [IsAffine G.X.left] (hG : Smooth G.X.hom)
    (i : P ⟶ G) (j : Q ⟶ G)
    (χ ψ : (Gm (Spec R)).toGrp ⟶ G)
    (hi : SubgroupFunctor.range i = parabolic χ)
    (hj : SubgroupFunctor.range j = parabolic ψ) (s : Spec R)
    (g₀ : Over.mk (𝟙 (Spec ((Spec R).residueField s))) ⟶
      ((baseChange ((Spec R).fromSpecResidueField s)).obj G).X)
    (hg₀ : PointwiseSchemeAction.IsTransporter
      ((baseChange ((Spec R).fromSpecResidueField s)).map ψ)
      ((baseChange ((Spec R).fromSpecResidueField s)).map χ) g₀) :
    EtaleSubgroupConjugacyData i j s :=
  Classical.choice <| by
    obtain ⟨U, p, hp, ⟨x, hx⟩, g, hg⟩ :=
      exists_etale_conjugacy_of_presentations hG i j χ ψ hi hj s g₀ hg₀
    exact ⟨⟨U, p, hp, x, hx, g, hg⟩⟩

end Dynamic

end Langlands.GroupScheme
