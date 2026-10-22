import Langlands.Representation.Twist.SubquotientStatement
import Mathlib.RepresentationTheory.Irreducible

namespace Langlands

universe uR uG uV

section Ring

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

@[simp]
theorem twistSubrepresentation_toSubmodule (chi : G →* Rˣ)
    {rho : Representation R G V} (S : Subrepresentation rho) :
    (twistSubrepresentation chi S).toSubmodule = S.toSubmodule := rfl

@[simp]
theorem twistSubrepresentation_bot (chi : G →* Rˣ) (rho : Representation R G V) :
    twistSubrepresentation chi (⊥ : Subrepresentation rho) = ⊥ :=
  (twistSubrepresentationOrderIso chi rho).map_bot

@[simp]
theorem twistSubrepresentation_top (chi : G →* Rˣ) (rho : Representation R G V) :
    twistSubrepresentation chi (⊤ : Subrepresentation rho) = ⊤ :=
  (twistSubrepresentationOrderIso chi rho).map_top

@[simp]
theorem twistSubrepresentation_sup (chi : G →* Rˣ)
    {rho : Representation R G V} (S T : Subrepresentation rho) :
    twistSubrepresentation chi (S ⊔ T) =
      twistSubrepresentation chi S ⊔ twistSubrepresentation chi T :=
  (twistSubrepresentationOrderIso chi rho).map_sup S T

@[simp]
theorem twistSubrepresentation_inf (chi : G →* Rˣ)
    {rho : Representation R G V} (S T : Subrepresentation rho) :
    twistSubrepresentation chi (S ⊓ T) =
      twistSubrepresentation chi S ⊓ twistSubrepresentation chi T :=
  (twistSubrepresentationOrderIso chi rho).map_inf S T

@[simp]
theorem twistSubrepresentationEquiv_apply (chi : G →* Rˣ)
    {rho : Representation R G V} (S : Subrepresentation rho) (v : S.toSubmodule) :
    twistSubrepresentationEquiv chi S v = v := rfl

@[simp]
theorem twistQuotientEquiv_mkQ (chi : G →* Rˣ)
    {rho : Representation R G V} (S : Subrepresentation rho) (v : V) :
    twistQuotientEquiv chi S (S.toSubmodule.mkQ v) = S.toSubmodule.mkQ v := rfl

theorem isSimpleOrder_twist_iff (chi : G →* Rˣ) (rho : Representation R G V) :
    IsSimpleOrder (Subrepresentation (twist chi rho)) ↔
      IsSimpleOrder (Subrepresentation rho) :=
  (twistSubrepresentationOrderIso chi rho).isSimpleOrder_iff.symm

theorem twistSubquotientLaws : TwistSubquotientLaws (R := R) (G := G) (V := V) := by
  intro chi rho
  exact ⟨twistSubrepresentation_toSubmodule chi,
    twistSubrepresentation_bot chi rho, twistSubrepresentation_top chi rho,
    twistSubrepresentation_sup chi, twistSubrepresentation_inf chi,
    twistSubrepresentationEquiv_apply chi, twistQuotientEquiv_mkQ chi,
    isSimpleOrder_twist_iff chi rho⟩

end Ring

section Field

variable {K : Type uR} {G : Type uG} {V : Type uV}
variable [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- Mathlib irreducibility is preserved by any scalar character twist. -/
theorem isIrreducible_twist_iff (chi : G →* Kˣ) (rho : Representation K G V) :
    Representation.IsIrreducible (twist chi rho) ↔ Representation.IsIrreducible rho :=
  isSimpleOrder_twist_iff chi rho

end Field

end Langlands
