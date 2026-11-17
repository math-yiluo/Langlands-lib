import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction
import Langlands.GroupScheme.BaseChangeReflection

/-! # Isomorphisms on residue fibres from isomorphisms on geometric fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace MaximalFibreSpreading

/-- A homomorphism of group schemes over `S` whose base change to the geometric point
over `s` is an isomorphism is already an isomorphism after base change to the residue
field of `s`. -/
theorem isIso_residueFibre_of_isIso_geometricFibre {S : Scheme.{u}} {P H : GroupScheme S}
    (f : P ⟶ H) (s : S)
    (h : IsIso ((GroupScheme.baseChange (geometricPoint S s)).map f)) :
    IsIso ((GroupScheme.baseChange (S.fromSpecResidueField s)).map f) := by
  let a := S.fromSpecResidueField s
  let b := toAlgebraicClosure (S.residueField s)
  have hnat := baseChangeCompIso_hom_naturality a b f
  have hb : IsIso ((GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map f)) := by
    have heq : (GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map f) =
        (baseChangeCompIso a b P).inv ≫ (GroupScheme.baseChange (b ≫ a)).map f ≫
          (baseChangeCompIso a b H).hom := by
      rw [hnat, Iso.inv_hom_id_assoc]
    rw [heq]
    have : IsIso ((GroupScheme.baseChange (b ≫ a)).map f) := h
    infer_instance
  obtain ⟨hbSurjective, hbFlat, hbQuasiCompact⟩ :=
    fieldExtension_fpqc (S.residueField s) (AlgebraicClosure (S.residueField s))
  let : Surjective b := hbSurjective
  let : Flat b := hbFlat
  let : QuasiCompact b := hbQuasiCompact
  exact isIso_of_baseChange b _

end MaximalFibreSpreading

end Langlands.GroupScheme
