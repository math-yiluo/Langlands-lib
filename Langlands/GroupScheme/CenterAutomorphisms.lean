import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.Reductive.Semisimple

/-! # Automorphisms fixing the full scheme-theoretic centre -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- The automorphism is the identity on every point of the full
scheme-theoretic centre, over every test scheme. -/
def AutomorphismFixesCenter (f : G ≅ G) : Prop :=
  ∀ (T : Over S) (z : T ⟶ G.X), z ∈ (center G).carrier T →
    z ≫ f.hom.hom.hom = z

namespace AutomorphismFixesCenter

/-- The identity automorphism fixes the full centre. -/
theorem refl : AutomorphismFixesCenter (Iso.refl G) := by
  intro T z _
  simp

/-- Centre-fixing automorphisms are closed under composition. -/
theorem trans {f g : G ≅ G} (hf : AutomorphismFixesCenter f)
    (hg : AutomorphismFixesCenter g) : AutomorphismFixesCenter (f.trans g) := by
  intro T z hz
  change z ≫ (f.hom.hom.hom ≫ g.hom.hom.hom) = z
  rw [← Category.assoc, hf T z hz, hg T z hz]

/-- The inverse of a centre-fixing automorphism fixes the full centre. -/
theorem symm {f : G ≅ G} (hf : AutomorphismFixesCenter f) :
    AutomorphismFixesCenter f.symm := by
  intro T z hz
  change z ≫ f.inv.hom.hom = z
  have h := hf T (z ≫ f.inv.hom.hom) (mem_center_comp_iso f.symm hz)
  simpa only [Category.assoc, ← Grp.comp_hom_hom, f.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id] using h.symm

/-- Inversion preserves and reflects pointwise fixation of the full centre. -/
theorem symm_iff (f : G ≅ G) :
    AutomorphismFixesCenter f.symm ↔ AutomorphismFixesCenter f :=
  ⟨fun h => h.symm, fun h => h.symm⟩

/-- Transporting an automorphism through an actual group-scheme isomorphism
preserves fixation of the full centre. -/
theorem conjugate {f : G ≅ G} (hf : AutomorphismFixesCenter f) (e : G ≅ H) :
    AutomorphismFixesCenter ((e.symm.trans f).trans e) := by
  intro T z hz
  change z ≫ (e.inv.hom.hom ≫ f.hom.hom.hom ≫ e.hom.hom.hom) = z
  rw [← Category.assoc, ← Category.assoc,
    hf T (z ≫ e.inv.hom.hom) (mem_center_comp_iso e.symm hz),
    Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id]

/-- Fixation of the full centre is invariant under change of group-scheme model. -/
theorem conjugate_iff (e : G ≅ H) (f : G ≅ G) :
    AutomorphismFixesCenter ((e.symm.trans f).trans e) ↔
      AutomorphismFixesCenter f := by
  constructor
  · intro h T z hz
    have he := h T (z ≫ e.hom.hom.hom) (mem_center_comp_iso e hz)
    change (z ≫ e.hom.hom.hom) ≫
      (e.inv.hom.hom ≫ f.hom.hom.hom ≫ e.hom.hom.hom) =
        z ≫ e.hom.hom.hom at he
    have hi := congrArg (fun x => x ≫ e.inv.hom.hom) he
    simpa only [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id_assoc, e.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id, Category.id_comp] using hi
  · exact fun h => h.conjugate e

/-- Every inner automorphism fixes the full scheme-theoretic centre. -/
theorem innerIso (g : Over.mk (𝟙 S) ⟶ G.X) :
    AutomorphismFixesCenter (G.innerIso g) := by
  intro T z hz
  rw [G.comp_innerIso_hom]
  have hc := (commute_of_mem_center hz (G.constantPoint g T)).symm
  rw [hc.eq, mul_inv_cancel_right]

/-- Composing on the left with a centre-fixing automorphism preserves and
reflects fixation of the full centre. -/
theorem trans_left_iff {f : G ≅ G} (hf : AutomorphismFixesCenter f) (g : G ≅ G) :
    AutomorphismFixesCenter (f.trans g) ↔ AutomorphismFixesCenter g := by
  constructor
  · intro h T z hz
    have he := h T z hz
    change z ≫ (f.hom.hom.hom ≫ g.hom.hom.hom) = z at he
    rwa [← Category.assoc, hf T z hz] at he
  · exact hf.trans

/-- Composing on the right with a centre-fixing automorphism preserves and
reflects fixation of the full centre. -/
theorem trans_right_iff (f : G ≅ G) {g : G ≅ G} (hg : AutomorphismFixesCenter g) :
    AutomorphismFixesCenter (f.trans g) ↔ AutomorphismFixesCenter f := by
  constructor
  · intro h T z hz
    have he := h T z hz
    change z ≫ (f.hom.hom.hom ≫ g.hom.hom.hom) = z at he
    rwa [← Category.assoc, hg T (z ≫ f.hom.hom.hom) (mem_center_comp_iso f hz)] at he
  · exact fun hf => hf.trans hg

end AutomorphismFixesCenter
end Langlands.GroupScheme
